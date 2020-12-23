%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:19 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 196 expanded)
%              Number of leaves         :   32 (  83 expanded)
%              Depth                    :   14
%              Number of atoms          :  139 ( 512 expanded)
%              Number of equality atoms :   26 (  90 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_40,axiom,(
    ! [A,B] : ~ v1_xboole_0(k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_xboole_0)).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
    <=> ( A = C
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(c_44,plain,(
    ! [A_35] : k2_tarski(A_35,A_35) = k1_tarski(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_11,B_12] : ~ v1_xboole_0(k2_tarski(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_49,plain,(
    ! [A_35] : ~ v1_xboole_0(k1_tarski(A_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_12])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_71,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_75,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_71])).

tff(c_42,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_132,plain,(
    ! [B_73,A_74] :
      ( r2_hidden(k4_tarski(B_73,k1_funct_1(A_74,B_73)),A_74)
      | ~ r2_hidden(B_73,k1_relat_1(A_74))
      | ~ v1_funct_1(A_74)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    ! [C_20,A_17,B_18] :
      ( r2_hidden(C_20,A_17)
      | ~ r2_hidden(C_20,B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_278,plain,(
    ! [B_110,A_111,A_112] :
      ( r2_hidden(k4_tarski(B_110,k1_funct_1(A_111,B_110)),A_112)
      | ~ m1_subset_1(A_111,k1_zfmisc_1(A_112))
      | ~ r2_hidden(B_110,k1_relat_1(A_111))
      | ~ v1_funct_1(A_111)
      | ~ v1_relat_1(A_111) ) ),
    inference(resolution,[status(thm)],[c_132,c_20])).

tff(c_18,plain,(
    ! [C_15,A_13,B_14,D_16] :
      ( C_15 = A_13
      | ~ r2_hidden(k4_tarski(A_13,B_14),k2_zfmisc_1(k1_tarski(C_15),D_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_350,plain,(
    ! [C_119,B_120,A_121,D_122] :
      ( C_119 = B_120
      | ~ m1_subset_1(A_121,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_119),D_122)))
      | ~ r2_hidden(B_120,k1_relat_1(A_121))
      | ~ v1_funct_1(A_121)
      | ~ v1_relat_1(A_121) ) ),
    inference(resolution,[status(thm)],[c_278,c_18])).

tff(c_352,plain,(
    ! [B_120] :
      ( B_120 = '#skF_2'
      | ~ r2_hidden(B_120,k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_350])).

tff(c_356,plain,(
    ! [B_123] :
      ( B_123 = '#skF_2'
      | ~ r2_hidden(B_123,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_42,c_352])).

tff(c_388,plain,
    ( '#skF_1'(k1_relat_1('#skF_4')) = '#skF_2'
    | v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_356])).

tff(c_420,plain,(
    v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_388])).

tff(c_123,plain,(
    ! [A_69,B_70] :
      ( k1_funct_1(A_69,B_70) = k1_xboole_0
      | r2_hidden(B_70,k1_relat_1(A_69))
      | ~ v1_funct_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_130,plain,(
    ! [A_69,B_70] :
      ( ~ v1_xboole_0(k1_relat_1(A_69))
      | k1_funct_1(A_69,B_70) = k1_xboole_0
      | ~ v1_funct_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(resolution,[status(thm)],[c_123,c_2])).

tff(c_424,plain,(
    ! [B_70] :
      ( k1_funct_1('#skF_4',B_70) = k1_xboole_0
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_420,c_130])).

tff(c_428,plain,(
    ! [B_70] : k1_funct_1('#skF_4',B_70) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_42,c_424])).

tff(c_34,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_430,plain,(
    ~ r2_hidden(k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_428,c_34])).

tff(c_40,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_431,plain,(
    ! [B_128] : k1_funct_1('#skF_4',B_128) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_42,c_424])).

tff(c_207,plain,(
    ! [D_93,C_94,B_95,A_96] :
      ( r2_hidden(k1_funct_1(D_93,C_94),B_95)
      | k1_xboole_0 = B_95
      | ~ r2_hidden(C_94,A_96)
      | ~ m1_subset_1(D_93,k1_zfmisc_1(k2_zfmisc_1(A_96,B_95)))
      | ~ v1_funct_2(D_93,A_96,B_95)
      | ~ v1_funct_1(D_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_225,plain,(
    ! [D_93,A_1,B_95] :
      ( r2_hidden(k1_funct_1(D_93,'#skF_1'(A_1)),B_95)
      | k1_xboole_0 = B_95
      | ~ m1_subset_1(D_93,k1_zfmisc_1(k2_zfmisc_1(A_1,B_95)))
      | ~ v1_funct_2(D_93,A_1,B_95)
      | ~ v1_funct_1(D_93)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_207])).

tff(c_437,plain,(
    ! [B_95,A_1] :
      ( r2_hidden(k1_xboole_0,B_95)
      | k1_xboole_0 = B_95
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_1,B_95)))
      | ~ v1_funct_2('#skF_4',A_1,B_95)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_225])).

tff(c_621,plain,(
    ! [B_143,A_144] :
      ( r2_hidden(k1_xboole_0,B_143)
      | k1_xboole_0 = B_143
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_144,B_143)))
      | ~ v1_funct_2('#skF_4',A_144,B_143)
      | v1_xboole_0(A_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_437])).

tff(c_624,plain,
    ( r2_hidden(k1_xboole_0,'#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3')
    | v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_621])).

tff(c_627,plain,
    ( r2_hidden(k1_xboole_0,'#skF_3')
    | k1_xboole_0 = '#skF_3'
    | v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_624])).

tff(c_629,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_36,c_430,c_627])).

tff(c_631,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_388])).

tff(c_630,plain,(
    '#skF_1'(k1_relat_1('#skF_4')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_388])).

tff(c_681,plain,
    ( v1_xboole_0(k1_relat_1('#skF_4'))
    | r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_630,c_4])).

tff(c_687,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_631,c_681])).

tff(c_16,plain,(
    ! [B_14,D_16,A_13,C_15] :
      ( r2_hidden(B_14,D_16)
      | ~ r2_hidden(k4_tarski(A_13,B_14),k2_zfmisc_1(k1_tarski(C_15),D_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_815,plain,(
    ! [A_175,B_176,D_177,C_178] :
      ( r2_hidden(k1_funct_1(A_175,B_176),D_177)
      | ~ m1_subset_1(A_175,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_178),D_177)))
      | ~ r2_hidden(B_176,k1_relat_1(A_175))
      | ~ v1_funct_1(A_175)
      | ~ v1_relat_1(A_175) ) ),
    inference(resolution,[status(thm)],[c_278,c_16])).

tff(c_817,plain,(
    ! [B_176] :
      ( r2_hidden(k1_funct_1('#skF_4',B_176),'#skF_3')
      | ~ r2_hidden(B_176,k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_815])).

tff(c_821,plain,(
    ! [B_179] :
      ( r2_hidden(k1_funct_1('#skF_4',B_179),'#skF_3')
      | ~ r2_hidden(B_179,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_42,c_817])).

tff(c_831,plain,(
    ~ r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_821,c_34])).

tff(c_841,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_687,c_831])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:59:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.07/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.61  
% 3.07/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.62  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.07/1.62  
% 3.07/1.62  %Foreground sorts:
% 3.07/1.62  
% 3.07/1.62  
% 3.07/1.62  %Background operators:
% 3.07/1.62  
% 3.07/1.62  
% 3.07/1.62  %Foreground operators:
% 3.07/1.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.07/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.07/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.07/1.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.07/1.62  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.07/1.62  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.07/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.07/1.62  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.07/1.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.07/1.62  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.07/1.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.07/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.07/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.07/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.07/1.62  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.07/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.07/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.07/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.07/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.07/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.07/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.07/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.07/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.07/1.62  
% 3.07/1.63  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.07/1.63  tff(f_40, axiom, (![A, B]: ~v1_xboole_0(k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_xboole_0)).
% 3.07/1.63  tff(f_99, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 3.07/1.63  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.07/1.63  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.07/1.63  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 3.07/1.63  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.07/1.63  tff(f_46, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 3.07/1.63  tff(f_87, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 3.07/1.63  tff(c_44, plain, (![A_35]: (k2_tarski(A_35, A_35)=k1_tarski(A_35))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.07/1.63  tff(c_12, plain, (![A_11, B_12]: (~v1_xboole_0(k2_tarski(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.07/1.63  tff(c_49, plain, (![A_35]: (~v1_xboole_0(k1_tarski(A_35)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_12])).
% 3.07/1.63  tff(c_36, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.07/1.63  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.07/1.63  tff(c_71, plain, (![C_42, A_43, B_44]: (v1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.07/1.63  tff(c_75, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_71])).
% 3.07/1.63  tff(c_42, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.07/1.63  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.07/1.63  tff(c_132, plain, (![B_73, A_74]: (r2_hidden(k4_tarski(B_73, k1_funct_1(A_74, B_73)), A_74) | ~r2_hidden(B_73, k1_relat_1(A_74)) | ~v1_funct_1(A_74) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.07/1.63  tff(c_20, plain, (![C_20, A_17, B_18]: (r2_hidden(C_20, A_17) | ~r2_hidden(C_20, B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.07/1.63  tff(c_278, plain, (![B_110, A_111, A_112]: (r2_hidden(k4_tarski(B_110, k1_funct_1(A_111, B_110)), A_112) | ~m1_subset_1(A_111, k1_zfmisc_1(A_112)) | ~r2_hidden(B_110, k1_relat_1(A_111)) | ~v1_funct_1(A_111) | ~v1_relat_1(A_111))), inference(resolution, [status(thm)], [c_132, c_20])).
% 3.07/1.63  tff(c_18, plain, (![C_15, A_13, B_14, D_16]: (C_15=A_13 | ~r2_hidden(k4_tarski(A_13, B_14), k2_zfmisc_1(k1_tarski(C_15), D_16)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.07/1.63  tff(c_350, plain, (![C_119, B_120, A_121, D_122]: (C_119=B_120 | ~m1_subset_1(A_121, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_119), D_122))) | ~r2_hidden(B_120, k1_relat_1(A_121)) | ~v1_funct_1(A_121) | ~v1_relat_1(A_121))), inference(resolution, [status(thm)], [c_278, c_18])).
% 3.07/1.63  tff(c_352, plain, (![B_120]: (B_120='#skF_2' | ~r2_hidden(B_120, k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_38, c_350])).
% 3.07/1.63  tff(c_356, plain, (![B_123]: (B_123='#skF_2' | ~r2_hidden(B_123, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_42, c_352])).
% 3.07/1.63  tff(c_388, plain, ('#skF_1'(k1_relat_1('#skF_4'))='#skF_2' | v1_xboole_0(k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_4, c_356])).
% 3.07/1.63  tff(c_420, plain, (v1_xboole_0(k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_388])).
% 3.07/1.63  tff(c_123, plain, (![A_69, B_70]: (k1_funct_1(A_69, B_70)=k1_xboole_0 | r2_hidden(B_70, k1_relat_1(A_69)) | ~v1_funct_1(A_69) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.07/1.63  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.07/1.63  tff(c_130, plain, (![A_69, B_70]: (~v1_xboole_0(k1_relat_1(A_69)) | k1_funct_1(A_69, B_70)=k1_xboole_0 | ~v1_funct_1(A_69) | ~v1_relat_1(A_69))), inference(resolution, [status(thm)], [c_123, c_2])).
% 3.07/1.63  tff(c_424, plain, (![B_70]: (k1_funct_1('#skF_4', B_70)=k1_xboole_0 | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_420, c_130])).
% 3.07/1.63  tff(c_428, plain, (![B_70]: (k1_funct_1('#skF_4', B_70)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_75, c_42, c_424])).
% 3.07/1.63  tff(c_34, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.07/1.63  tff(c_430, plain, (~r2_hidden(k1_xboole_0, '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_428, c_34])).
% 3.07/1.63  tff(c_40, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.07/1.63  tff(c_431, plain, (![B_128]: (k1_funct_1('#skF_4', B_128)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_75, c_42, c_424])).
% 3.07/1.63  tff(c_207, plain, (![D_93, C_94, B_95, A_96]: (r2_hidden(k1_funct_1(D_93, C_94), B_95) | k1_xboole_0=B_95 | ~r2_hidden(C_94, A_96) | ~m1_subset_1(D_93, k1_zfmisc_1(k2_zfmisc_1(A_96, B_95))) | ~v1_funct_2(D_93, A_96, B_95) | ~v1_funct_1(D_93))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.07/1.63  tff(c_225, plain, (![D_93, A_1, B_95]: (r2_hidden(k1_funct_1(D_93, '#skF_1'(A_1)), B_95) | k1_xboole_0=B_95 | ~m1_subset_1(D_93, k1_zfmisc_1(k2_zfmisc_1(A_1, B_95))) | ~v1_funct_2(D_93, A_1, B_95) | ~v1_funct_1(D_93) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_207])).
% 3.07/1.63  tff(c_437, plain, (![B_95, A_1]: (r2_hidden(k1_xboole_0, B_95) | k1_xboole_0=B_95 | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_1, B_95))) | ~v1_funct_2('#skF_4', A_1, B_95) | ~v1_funct_1('#skF_4') | v1_xboole_0(A_1))), inference(superposition, [status(thm), theory('equality')], [c_431, c_225])).
% 3.07/1.63  tff(c_621, plain, (![B_143, A_144]: (r2_hidden(k1_xboole_0, B_143) | k1_xboole_0=B_143 | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_144, B_143))) | ~v1_funct_2('#skF_4', A_144, B_143) | v1_xboole_0(A_144))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_437])).
% 3.07/1.63  tff(c_624, plain, (r2_hidden(k1_xboole_0, '#skF_3') | k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3') | v1_xboole_0(k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_621])).
% 3.07/1.63  tff(c_627, plain, (r2_hidden(k1_xboole_0, '#skF_3') | k1_xboole_0='#skF_3' | v1_xboole_0(k1_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_624])).
% 3.07/1.63  tff(c_629, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_36, c_430, c_627])).
% 3.07/1.63  tff(c_631, plain, (~v1_xboole_0(k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_388])).
% 3.07/1.63  tff(c_630, plain, ('#skF_1'(k1_relat_1('#skF_4'))='#skF_2'), inference(splitRight, [status(thm)], [c_388])).
% 3.07/1.63  tff(c_681, plain, (v1_xboole_0(k1_relat_1('#skF_4')) | r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_630, c_4])).
% 3.07/1.63  tff(c_687, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_631, c_681])).
% 3.07/1.63  tff(c_16, plain, (![B_14, D_16, A_13, C_15]: (r2_hidden(B_14, D_16) | ~r2_hidden(k4_tarski(A_13, B_14), k2_zfmisc_1(k1_tarski(C_15), D_16)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.07/1.63  tff(c_815, plain, (![A_175, B_176, D_177, C_178]: (r2_hidden(k1_funct_1(A_175, B_176), D_177) | ~m1_subset_1(A_175, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_178), D_177))) | ~r2_hidden(B_176, k1_relat_1(A_175)) | ~v1_funct_1(A_175) | ~v1_relat_1(A_175))), inference(resolution, [status(thm)], [c_278, c_16])).
% 3.07/1.63  tff(c_817, plain, (![B_176]: (r2_hidden(k1_funct_1('#skF_4', B_176), '#skF_3') | ~r2_hidden(B_176, k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_38, c_815])).
% 3.07/1.63  tff(c_821, plain, (![B_179]: (r2_hidden(k1_funct_1('#skF_4', B_179), '#skF_3') | ~r2_hidden(B_179, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_42, c_817])).
% 3.07/1.63  tff(c_831, plain, (~r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_821, c_34])).
% 3.07/1.63  tff(c_841, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_687, c_831])).
% 3.07/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.63  
% 3.07/1.63  Inference rules
% 3.07/1.63  ----------------------
% 3.07/1.63  #Ref     : 0
% 3.07/1.63  #Sup     : 169
% 3.07/1.63  #Fact    : 0
% 3.07/1.63  #Define  : 0
% 3.07/1.63  #Split   : 7
% 3.07/1.63  #Chain   : 0
% 3.07/1.63  #Close   : 0
% 3.07/1.63  
% 3.07/1.63  Ordering : KBO
% 3.07/1.63  
% 3.07/1.63  Simplification rules
% 3.07/1.63  ----------------------
% 3.07/1.63  #Subsume      : 24
% 3.07/1.63  #Demod        : 37
% 3.07/1.63  #Tautology    : 22
% 3.07/1.63  #SimpNegUnit  : 6
% 3.07/1.63  #BackRed      : 1
% 3.07/1.63  
% 3.07/1.63  #Partial instantiations: 0
% 3.07/1.63  #Strategies tried      : 1
% 3.07/1.63  
% 3.07/1.63  Timing (in seconds)
% 3.07/1.63  ----------------------
% 3.07/1.63  Preprocessing        : 0.40
% 3.07/1.63  Parsing              : 0.23
% 3.07/1.63  CNF conversion       : 0.02
% 3.07/1.63  Main loop            : 0.39
% 3.07/1.63  Inferencing          : 0.15
% 3.07/1.63  Reduction            : 0.10
% 3.07/1.63  Demodulation         : 0.07
% 3.07/1.63  BG Simplification    : 0.02
% 3.07/1.63  Subsumption          : 0.09
% 3.07/1.63  Abstraction          : 0.02
% 3.07/1.63  MUC search           : 0.00
% 3.07/1.63  Cooper               : 0.00
% 3.07/1.63  Total                : 0.82
% 3.07/1.63  Index Insertion      : 0.00
% 3.07/1.63  Index Deletion       : 0.00
% 3.07/1.63  Index Matching       : 0.00
% 3.07/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
