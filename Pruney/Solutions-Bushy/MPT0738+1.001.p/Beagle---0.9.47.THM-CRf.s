%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0738+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:47 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 284 expanded)
%              Number of leaves         :   24 ( 106 expanded)
%              Depth                    :   13
%              Number of atoms          :  174 ( 774 expanded)
%              Number of equality atoms :   10 (  54 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > m1_subset_1 > v3_ordinal1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r1_ordinal1(A,B)
              | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_67,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_95,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_36,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_34,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_113,plain,(
    ! [B_57,A_58] :
      ( r1_ordinal1(B_57,A_58)
      | r1_ordinal1(A_58,B_57)
      | ~ v3_ordinal1(B_57)
      | ~ v3_ordinal1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_32,plain,(
    ~ r1_ordinal1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_116,plain,
    ( r1_ordinal1('#skF_3','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_113,c_32])).

tff(c_122,plain,(
    r1_ordinal1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36,c_116])).

tff(c_167,plain,(
    ! [B_70,A_71] :
      ( r2_hidden(B_70,A_71)
      | B_70 = A_71
      | r2_hidden(A_71,B_70)
      | ~ v3_ordinal1(B_70)
      | ~ v3_ordinal1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_26,plain,(
    ! [B_25,A_24] :
      ( ~ v1_xboole_0(B_25)
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_247,plain,(
    ! [B_78,A_79] :
      ( ~ v1_xboole_0(B_78)
      | r2_hidden(B_78,A_79)
      | B_78 = A_79
      | ~ v3_ordinal1(B_78)
      | ~ v3_ordinal1(A_79) ) ),
    inference(resolution,[status(thm)],[c_167,c_26])).

tff(c_30,plain,(
    ~ r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_273,plain,
    ( ~ v1_xboole_0('#skF_3')
    | '#skF_2' = '#skF_3'
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_247,c_30])).

tff(c_284,plain,
    ( ~ v1_xboole_0('#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_273])).

tff(c_285,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_284])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_394,plain,(
    ! [A_91,B_92] :
      ( m1_subset_1(A_91,B_92)
      | r2_hidden(B_92,A_91)
      | B_92 = A_91
      | ~ v3_ordinal1(B_92)
      | ~ v3_ordinal1(A_91) ) ),
    inference(resolution,[status(thm)],[c_167,c_12])).

tff(c_420,plain,
    ( m1_subset_1('#skF_2','#skF_3')
    | '#skF_2' = '#skF_3'
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_394,c_30])).

tff(c_431,plain,
    ( m1_subset_1('#skF_2','#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_420])).

tff(c_432,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_431])).

tff(c_433,plain,(
    r1_ordinal1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_122])).

tff(c_435,plain,(
    ~ r1_ordinal1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_32])).

tff(c_444,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_435])).

tff(c_445,plain,(
    m1_subset_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_431])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ r1_ordinal1(A_7,B_8)
      | ~ v3_ordinal1(B_8)
      | ~ v3_ordinal1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( r2_hidden(A_14,B_15)
      | v1_xboole_0(B_15)
      | ~ m1_subset_1(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_71,plain,(
    ! [C_45,B_46,A_47] :
      ( ~ v1_xboole_0(C_45)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(C_45))
      | ~ r2_hidden(A_47,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_90,plain,(
    ! [B_52,A_53,A_54] :
      ( ~ v1_xboole_0(B_52)
      | ~ r2_hidden(A_53,A_54)
      | ~ r1_tarski(A_54,B_52) ) ),
    inference(resolution,[status(thm)],[c_20,c_71])).

tff(c_240,plain,(
    ! [B_75,B_76,A_77] :
      ( ~ v1_xboole_0(B_75)
      | ~ r1_tarski(B_76,B_75)
      | v1_xboole_0(B_76)
      | ~ m1_subset_1(A_77,B_76) ) ),
    inference(resolution,[status(thm)],[c_16,c_90])).

tff(c_698,plain,(
    ! [B_121,A_122,A_123] :
      ( ~ v1_xboole_0(B_121)
      | v1_xboole_0(A_122)
      | ~ m1_subset_1(A_123,A_122)
      | ~ r1_ordinal1(A_122,B_121)
      | ~ v3_ordinal1(B_121)
      | ~ v3_ordinal1(A_122) ) ),
    inference(resolution,[status(thm)],[c_10,c_240])).

tff(c_708,plain,(
    ! [B_121] :
      ( ~ v1_xboole_0(B_121)
      | v1_xboole_0('#skF_3')
      | ~ r1_ordinal1('#skF_3',B_121)
      | ~ v3_ordinal1(B_121)
      | ~ v3_ordinal1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_445,c_698])).

tff(c_721,plain,(
    ! [B_121] :
      ( ~ v1_xboole_0(B_121)
      | v1_xboole_0('#skF_3')
      | ~ r1_ordinal1('#skF_3',B_121)
      | ~ v3_ordinal1(B_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_708])).

tff(c_726,plain,(
    ! [B_124] :
      ( ~ v1_xboole_0(B_124)
      | ~ r1_ordinal1('#skF_3',B_124)
      | ~ v3_ordinal1(B_124) ) ),
    inference(negUnitSimplification,[status(thm)],[c_285,c_721])).

tff(c_733,plain,
    ( ~ v1_xboole_0('#skF_2')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_122,c_726])).

tff(c_747,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_733])).

tff(c_133,plain,(
    ! [A_62,C_63,B_64] :
      ( m1_subset_1(A_62,C_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(C_63))
      | ~ r2_hidden(A_62,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_147,plain,(
    ! [A_67,B_68,A_69] :
      ( m1_subset_1(A_67,B_68)
      | ~ r2_hidden(A_67,A_69)
      | ~ r1_tarski(A_69,B_68) ) ),
    inference(resolution,[status(thm)],[c_20,c_133])).

tff(c_480,plain,(
    ! [A_95,B_96,B_97] :
      ( m1_subset_1(A_95,B_96)
      | ~ r1_tarski(B_97,B_96)
      | v1_xboole_0(B_97)
      | ~ m1_subset_1(A_95,B_97) ) ),
    inference(resolution,[status(thm)],[c_16,c_147])).

tff(c_928,plain,(
    ! [A_144,B_145,A_146] :
      ( m1_subset_1(A_144,B_145)
      | v1_xboole_0(A_146)
      | ~ m1_subset_1(A_144,A_146)
      | ~ r1_ordinal1(A_146,B_145)
      | ~ v3_ordinal1(B_145)
      | ~ v3_ordinal1(A_146) ) ),
    inference(resolution,[status(thm)],[c_10,c_480])).

tff(c_938,plain,(
    ! [B_145] :
      ( m1_subset_1('#skF_2',B_145)
      | v1_xboole_0('#skF_3')
      | ~ r1_ordinal1('#skF_3',B_145)
      | ~ v3_ordinal1(B_145)
      | ~ v3_ordinal1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_445,c_928])).

tff(c_951,plain,(
    ! [B_145] :
      ( m1_subset_1('#skF_2',B_145)
      | v1_xboole_0('#skF_3')
      | ~ r1_ordinal1('#skF_3',B_145)
      | ~ v3_ordinal1(B_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_938])).

tff(c_956,plain,(
    ! [B_147] :
      ( m1_subset_1('#skF_2',B_147)
      | ~ r1_ordinal1('#skF_3',B_147)
      | ~ v3_ordinal1(B_147) ) ),
    inference(negUnitSimplification,[status(thm)],[c_285,c_951])).

tff(c_971,plain,
    ( m1_subset_1('#skF_2','#skF_2')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_122,c_956])).

tff(c_991,plain,(
    m1_subset_1('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_971])).

tff(c_54,plain,(
    ! [A_43,B_44] :
      ( r2_hidden(A_43,B_44)
      | v1_xboole_0(B_44)
      | ~ m1_subset_1(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_85,plain,(
    ! [B_50,A_51] :
      ( ~ r2_hidden(B_50,A_51)
      | v1_xboole_0(B_50)
      | ~ m1_subset_1(A_51,B_50) ) ),
    inference(resolution,[status(thm)],[c_54,c_2])).

tff(c_89,plain,(
    ! [A_14,B_15] :
      ( v1_xboole_0(A_14)
      | ~ m1_subset_1(B_15,A_14)
      | v1_xboole_0(B_15)
      | ~ m1_subset_1(A_14,B_15) ) ),
    inference(resolution,[status(thm)],[c_16,c_85])).

tff(c_1001,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_991,c_89])).

tff(c_1008,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_991,c_1001])).

tff(c_1010,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_747,c_1008])).

tff(c_1011,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_284])).

tff(c_1013,plain,(
    r1_ordinal1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1011,c_122])).

tff(c_1015,plain,(
    ~ r1_ordinal1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1011,c_32])).

tff(c_1027,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1013,c_1015])).

%------------------------------------------------------------------------------
