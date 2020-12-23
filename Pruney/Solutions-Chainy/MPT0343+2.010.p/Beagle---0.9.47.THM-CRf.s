%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:18 EST 2020

% Result     : Theorem 5.15s
% Output     : CNFRefutation 5.23s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 912 expanded)
%              Number of leaves         :   21 ( 287 expanded)
%              Depth                    :   15
%              Number of atoms          :  331 (2505 expanded)
%              Number of equality atoms :   20 ( 145 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ! [D] :
                  ( m1_subset_1(D,A)
                 => ( r2_hidden(D,B)
                  <=> r2_hidden(D,C) ) )
             => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

tff(c_30,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_24,plain,(
    ! [B_15,A_14] :
      ( m1_subset_1(B_15,A_14)
      | ~ v1_xboole_0(B_15)
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_117,plain,(
    ! [D_47] :
      ( r2_hidden(D_47,'#skF_4')
      | ~ r2_hidden(D_47,'#skF_5')
      | ~ m1_subset_1(D_47,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_131,plain,
    ( r2_hidden('#skF_1'('#skF_5'),'#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_3')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_117])).

tff(c_3333,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_131])).

tff(c_3340,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_5'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_3333])).

tff(c_3347,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3340])).

tff(c_68,plain,(
    ! [B_38,A_39] :
      ( m1_subset_1(B_38,A_39)
      | ~ r2_hidden(B_38,A_39)
      | v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_76,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_68])).

tff(c_22,plain,(
    ! [B_15,A_14] :
      ( r2_hidden(B_15,A_14)
      | ~ m1_subset_1(B_15,A_14)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_57,plain,(
    ! [D_35] :
      ( r2_hidden(D_35,'#skF_5')
      | ~ r2_hidden(D_35,'#skF_4')
      | ~ m1_subset_1(D_35,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_61,plain,(
    ! [D_35] :
      ( ~ v1_xboole_0('#skF_5')
      | ~ r2_hidden(D_35,'#skF_4')
      | ~ m1_subset_1(D_35,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_57,c_2])).

tff(c_187,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_61])).

tff(c_188,plain,
    ( r2_hidden('#skF_1'('#skF_5'),'#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_131])).

tff(c_189,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_188])).

tff(c_193,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_5'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_189])).

tff(c_194,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_193])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_221,plain,(
    ! [C_66,A_67,B_68] :
      ( r2_hidden(C_66,A_67)
      | ~ r2_hidden(C_66,B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_479,plain,(
    ! [B_94,A_95,A_96] :
      ( r2_hidden(B_94,A_95)
      | ~ m1_subset_1(A_96,k1_zfmisc_1(A_95))
      | ~ m1_subset_1(B_94,A_96)
      | v1_xboole_0(A_96) ) ),
    inference(resolution,[status(thm)],[c_22,c_221])).

tff(c_493,plain,(
    ! [B_94] :
      ( r2_hidden(B_94,'#skF_3')
      | ~ m1_subset_1(B_94,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_32,c_479])).

tff(c_506,plain,(
    ! [B_97] :
      ( r2_hidden(B_97,'#skF_3')
      | ~ m1_subset_1(B_97,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_493])).

tff(c_20,plain,(
    ! [B_15,A_14] :
      ( m1_subset_1(B_15,A_14)
      | ~ r2_hidden(B_15,A_14)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_517,plain,(
    ! [B_97] :
      ( m1_subset_1(B_97,'#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(B_97,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_506,c_20])).

tff(c_550,plain,(
    ! [B_99] :
      ( m1_subset_1(B_99,'#skF_3')
      | ~ m1_subset_1(B_99,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_517])).

tff(c_565,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),'#skF_3')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_550])).

tff(c_580,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_189,c_565])).

tff(c_582,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_193])).

tff(c_640,plain,(
    ! [C_106,A_107,B_108] :
      ( r2_hidden(C_106,A_107)
      | ~ r2_hidden(C_106,B_108)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(A_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_662,plain,(
    ! [A_111,A_112] :
      ( r2_hidden('#skF_1'(A_111),A_112)
      | ~ m1_subset_1(A_111,k1_zfmisc_1(A_112))
      | v1_xboole_0(A_111) ) ),
    inference(resolution,[status(thm)],[c_4,c_640])).

tff(c_687,plain,(
    ! [A_113,A_114] :
      ( ~ v1_xboole_0(A_113)
      | ~ m1_subset_1(A_114,k1_zfmisc_1(A_113))
      | v1_xboole_0(A_114) ) ),
    inference(resolution,[status(thm)],[c_662,c_2])).

tff(c_698,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_687])).

tff(c_706,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_582,c_698])).

tff(c_708,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_706])).

tff(c_709,plain,(
    r2_hidden('#skF_1'('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_742,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_709,c_2])).

tff(c_132,plain,(
    ! [A_48,B_49] :
      ( r2_hidden('#skF_2'(A_48,B_49),A_48)
      | r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_149,plain,(
    ! [A_48,B_49] :
      ( m1_subset_1('#skF_2'(A_48,B_49),A_48)
      | v1_xboole_0(A_48)
      | r1_tarski(A_48,B_49) ) ),
    inference(resolution,[status(thm)],[c_132,c_20])).

tff(c_710,plain,(
    m1_subset_1('#skF_1'('#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_26,plain,(
    ! [B_15,A_14] :
      ( v1_xboole_0(B_15)
      | ~ m1_subset_1(B_15,A_14)
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_746,plain,
    ( v1_xboole_0('#skF_1'('#skF_5'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_710,c_26])).

tff(c_747,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_746])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_748,plain,(
    ! [C_116,A_117,B_118] :
      ( r2_hidden(C_116,A_117)
      | ~ r2_hidden(C_116,B_118)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(A_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1670,plain,(
    ! [B_188,A_189,A_190] :
      ( r2_hidden(B_188,A_189)
      | ~ m1_subset_1(A_190,k1_zfmisc_1(A_189))
      | ~ m1_subset_1(B_188,A_190)
      | v1_xboole_0(A_190) ) ),
    inference(resolution,[status(thm)],[c_22,c_748])).

tff(c_1692,plain,(
    ! [B_188] :
      ( r2_hidden(B_188,'#skF_3')
      | ~ m1_subset_1(B_188,'#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_1670])).

tff(c_1727,plain,(
    ! [B_192] :
      ( r2_hidden(B_192,'#skF_3')
      | ~ m1_subset_1(B_192,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_742,c_1692])).

tff(c_1738,plain,(
    ! [B_192] :
      ( m1_subset_1(B_192,'#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(B_192,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1727,c_20])).

tff(c_1747,plain,(
    ! [B_192] :
      ( m1_subset_1(B_192,'#skF_3')
      | ~ m1_subset_1(B_192,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_747,c_1738])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_38,plain,(
    ! [D_24] :
      ( r2_hidden(D_24,'#skF_5')
      | ~ r2_hidden(D_24,'#skF_4')
      | ~ m1_subset_1(D_24,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_106,plain,(
    ! [A_45,B_46] :
      ( ~ r2_hidden('#skF_2'(A_45,B_46),B_46)
      | r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2051,plain,(
    ! [A_205] :
      ( r1_tarski(A_205,'#skF_5')
      | ~ r2_hidden('#skF_2'(A_205,'#skF_5'),'#skF_4')
      | ~ m1_subset_1('#skF_2'(A_205,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_106])).

tff(c_2079,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_4','#skF_5'),'#skF_3')
    | r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_2051])).

tff(c_2083,plain,(
    ~ m1_subset_1('#skF_2'('#skF_4','#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2079])).

tff(c_2090,plain,(
    ~ m1_subset_1('#skF_2'('#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1747,c_2083])).

tff(c_2094,plain,
    ( v1_xboole_0('#skF_4')
    | r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_149,c_2090])).

tff(c_2100,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_742,c_2094])).

tff(c_91,plain,(
    ! [A_43,B_44] :
      ( r2_xboole_0(A_43,B_44)
      | B_44 = A_43
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( ~ r2_xboole_0(B_13,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_102,plain,(
    ! [B_44,A_43] :
      ( ~ r1_tarski(B_44,A_43)
      | B_44 = A_43
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(resolution,[status(thm)],[c_91,c_18])).

tff(c_2142,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_2100,c_102])).

tff(c_2158,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_2142])).

tff(c_1690,plain,(
    ! [B_188] :
      ( r2_hidden(B_188,'#skF_3')
      | ~ m1_subset_1(B_188,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_32,c_1670])).

tff(c_1705,plain,(
    ! [B_191] :
      ( r2_hidden(B_191,'#skF_3')
      | ~ m1_subset_1(B_191,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_1690])).

tff(c_1716,plain,(
    ! [B_191] :
      ( m1_subset_1(B_191,'#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(B_191,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1705,c_20])).

tff(c_1749,plain,(
    ! [B_193] :
      ( m1_subset_1(B_193,'#skF_3')
      | ~ m1_subset_1(B_193,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_747,c_1716])).

tff(c_1768,plain,(
    ! [B_49] :
      ( m1_subset_1('#skF_2'('#skF_5',B_49),'#skF_3')
      | v1_xboole_0('#skF_5')
      | r1_tarski('#skF_5',B_49) ) ),
    inference(resolution,[status(thm)],[c_149,c_1749])).

tff(c_2336,plain,(
    ! [B_215] :
      ( m1_subset_1('#skF_2'('#skF_5',B_215),'#skF_3')
      | r1_tarski('#skF_5',B_215) ) ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_1768])).

tff(c_36,plain,(
    ! [D_24] :
      ( r2_hidden(D_24,'#skF_4')
      | ~ r2_hidden(D_24,'#skF_5')
      | ~ m1_subset_1(D_24,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1615,plain,(
    ! [B_180] :
      ( r2_hidden('#skF_2'('#skF_5',B_180),'#skF_4')
      | ~ m1_subset_1('#skF_2'('#skF_5',B_180),'#skF_3')
      | r1_tarski('#skF_5',B_180) ) ),
    inference(resolution,[status(thm)],[c_132,c_36])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1639,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_5','#skF_4'),'#skF_3')
    | r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1615,c_8])).

tff(c_1644,plain,(
    ~ m1_subset_1('#skF_2'('#skF_5','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1639])).

tff(c_2339,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_2336,c_1644])).

tff(c_2350,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2158,c_2339])).

tff(c_2351,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_2079])).

tff(c_2371,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_2351,c_102])).

tff(c_2387,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_2371])).

tff(c_2558,plain,(
    ! [B_224] :
      ( m1_subset_1('#skF_2'('#skF_5',B_224),'#skF_3')
      | r1_tarski('#skF_5',B_224) ) ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_1768])).

tff(c_2561,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_2558,c_1644])).

tff(c_2572,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2387,c_2561])).

tff(c_2573,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1639])).

tff(c_2587,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_2573,c_102])).

tff(c_2596,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_2587])).

tff(c_2802,plain,(
    ! [B_239,A_240,A_241] :
      ( r2_hidden(B_239,A_240)
      | ~ m1_subset_1(A_241,k1_zfmisc_1(A_240))
      | ~ m1_subset_1(B_239,A_241)
      | v1_xboole_0(A_241) ) ),
    inference(resolution,[status(thm)],[c_22,c_748])).

tff(c_2824,plain,(
    ! [B_239] :
      ( r2_hidden(B_239,'#skF_3')
      | ~ m1_subset_1(B_239,'#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_2802])).

tff(c_2859,plain,(
    ! [B_243] :
      ( r2_hidden(B_243,'#skF_3')
      | ~ m1_subset_1(B_243,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_742,c_2824])).

tff(c_2870,plain,(
    ! [B_243] :
      ( m1_subset_1(B_243,'#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(B_243,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2859,c_20])).

tff(c_2972,plain,(
    ! [B_246] :
      ( m1_subset_1(B_246,'#skF_3')
      | ~ m1_subset_1(B_246,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_747,c_2870])).

tff(c_2933,plain,(
    ! [A_245] :
      ( r1_tarski(A_245,'#skF_5')
      | ~ r2_hidden('#skF_2'(A_245,'#skF_5'),'#skF_4')
      | ~ m1_subset_1('#skF_2'(A_245,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_106])).

tff(c_2951,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_4','#skF_5'),'#skF_3')
    | r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_2933])).

tff(c_2964,plain,(
    ~ m1_subset_1('#skF_2'('#skF_4','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_2596,c_2596,c_2951])).

tff(c_2983,plain,(
    ~ m1_subset_1('#skF_2'('#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_2972,c_2964])).

tff(c_2990,plain,
    ( v1_xboole_0('#skF_4')
    | r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_149,c_2983])).

tff(c_2997,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2596,c_742,c_2990])).

tff(c_2999,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_746])).

tff(c_2998,plain,(
    v1_xboole_0('#skF_1'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_746])).

tff(c_150,plain,(
    ! [A_48,B_49] :
      ( ~ v1_xboole_0(A_48)
      | r1_tarski(A_48,B_49) ) ),
    inference(resolution,[status(thm)],[c_132,c_2])).

tff(c_153,plain,(
    ! [B_53,A_54] :
      ( ~ r1_tarski(B_53,A_54)
      | B_53 = A_54
      | ~ r1_tarski(A_54,B_53) ) ),
    inference(resolution,[status(thm)],[c_91,c_18])).

tff(c_163,plain,(
    ! [B_55,A_56] :
      ( B_55 = A_56
      | ~ r1_tarski(B_55,A_56)
      | ~ v1_xboole_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_150,c_153])).

tff(c_170,plain,(
    ! [B_49,A_48] :
      ( B_49 = A_48
      | ~ v1_xboole_0(B_49)
      | ~ v1_xboole_0(A_48) ) ),
    inference(resolution,[status(thm)],[c_150,c_163])).

tff(c_3022,plain,(
    ! [A_250] :
      ( A_250 = '#skF_3'
      | ~ v1_xboole_0(A_250) ) ),
    inference(resolution,[status(thm)],[c_2999,c_170])).

tff(c_3029,plain,(
    '#skF_1'('#skF_5') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2998,c_3022])).

tff(c_3034,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3029,c_709])).

tff(c_28,plain,(
    ! [C_19,A_16,B_17] :
      ( r2_hidden(C_19,A_16)
      | ~ r2_hidden(C_19,B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3304,plain,(
    ! [A_264] :
      ( r2_hidden('#skF_3',A_264)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_264)) ) ),
    inference(resolution,[status(thm)],[c_3034,c_28])).

tff(c_3312,plain,(
    r2_hidden('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_3304])).

tff(c_3322,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_3312,c_2])).

tff(c_3330,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2999,c_3322])).

tff(c_3361,plain,(
    ! [D_269] :
      ( ~ r2_hidden(D_269,'#skF_4')
      | ~ m1_subset_1(D_269,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_3375,plain,(
    ! [B_15] :
      ( ~ m1_subset_1(B_15,'#skF_3')
      | ~ m1_subset_1(B_15,'#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_3361])).

tff(c_3389,plain,(
    ! [B_271] :
      ( ~ m1_subset_1(B_271,'#skF_3')
      | ~ m1_subset_1(B_271,'#skF_4') ) ),
    inference(splitLeft,[status(thm)],[c_3375])).

tff(c_3393,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_3'),'#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_3389])).

tff(c_3400,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_3347,c_3393])).

tff(c_3405,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_3'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_3400])).

tff(c_3406,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3405])).

tff(c_3348,plain,(
    ! [C_266,A_267,B_268] :
      ( r2_hidden(C_266,A_267)
      | ~ r2_hidden(C_266,B_268)
      | ~ m1_subset_1(B_268,k1_zfmisc_1(A_267)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3649,plain,(
    ! [B_299,A_300,A_301] :
      ( r2_hidden(B_299,A_300)
      | ~ m1_subset_1(A_301,k1_zfmisc_1(A_300))
      | ~ m1_subset_1(B_299,A_301)
      | v1_xboole_0(A_301) ) ),
    inference(resolution,[status(thm)],[c_22,c_3348])).

tff(c_3662,plain,(
    ! [B_299] :
      ( r2_hidden(B_299,'#skF_3')
      | ~ m1_subset_1(B_299,'#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_3649])).

tff(c_3671,plain,(
    ! [B_302] :
      ( r2_hidden(B_302,'#skF_3')
      | ~ m1_subset_1(B_302,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_3406,c_3662])).

tff(c_3682,plain,(
    ! [B_302] :
      ( m1_subset_1(B_302,'#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(B_302,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3671,c_20])).

tff(c_3693,plain,(
    ! [B_303] :
      ( m1_subset_1(B_303,'#skF_3')
      | ~ m1_subset_1(B_303,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_3347,c_3682])).

tff(c_3388,plain,(
    ! [B_15] :
      ( ~ m1_subset_1(B_15,'#skF_3')
      | ~ m1_subset_1(B_15,'#skF_4') ) ),
    inference(splitLeft,[status(thm)],[c_3375])).

tff(c_3729,plain,(
    ! [B_304] : ~ m1_subset_1(B_304,'#skF_4') ),
    inference(resolution,[status(thm)],[c_3693,c_3388])).

tff(c_3737,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_3729])).

tff(c_3748,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3406,c_3737])).

tff(c_3750,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_3405])).

tff(c_3332,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_3336,plain,(
    ! [A_48] :
      ( A_48 = '#skF_5'
      | ~ v1_xboole_0(A_48) ) ),
    inference(resolution,[status(thm)],[c_3332,c_170])).

tff(c_3754,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3750,c_3336])).

tff(c_3760,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_3754])).

tff(c_3761,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_3375])).

tff(c_3764,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3761,c_3336])).

tff(c_3770,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_3764])).

tff(c_3772,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_3340])).

tff(c_3778,plain,(
    '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3772,c_3336])).

tff(c_3786,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3778,c_30])).

tff(c_3825,plain,(
    ! [D_309] :
      ( ~ r2_hidden(D_309,'#skF_4')
      | ~ m1_subset_1(D_309,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_3839,plain,(
    ! [B_15] :
      ( ~ m1_subset_1(B_15,'#skF_3')
      | ~ m1_subset_1(B_15,'#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_3825])).

tff(c_3886,plain,(
    ! [B_316] :
      ( ~ m1_subset_1(B_316,'#skF_3')
      | ~ m1_subset_1(B_316,'#skF_4') ) ),
    inference(splitLeft,[status(thm)],[c_3839])).

tff(c_3894,plain,(
    ! [B_15] :
      ( ~ m1_subset_1(B_15,'#skF_4')
      | ~ v1_xboole_0(B_15)
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_3886])).

tff(c_3900,plain,(
    ! [B_317] :
      ( ~ m1_subset_1(B_317,'#skF_4')
      | ~ v1_xboole_0(B_317) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3772,c_3894])).

tff(c_3910,plain,(
    ! [B_15] :
      ( ~ v1_xboole_0(B_15)
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_3900])).

tff(c_3911,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3910])).

tff(c_3792,plain,(
    ! [C_305,A_306,B_307] :
      ( r2_hidden(C_305,A_306)
      | ~ r2_hidden(C_305,B_307)
      | ~ m1_subset_1(B_307,k1_zfmisc_1(A_306)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3979,plain,(
    ! [A_325,A_326] :
      ( r2_hidden('#skF_1'(A_325),A_326)
      | ~ m1_subset_1(A_325,k1_zfmisc_1(A_326))
      | v1_xboole_0(A_325) ) ),
    inference(resolution,[status(thm)],[c_4,c_3792])).

tff(c_4004,plain,(
    ! [A_327,A_328] :
      ( ~ v1_xboole_0(A_327)
      | ~ m1_subset_1(A_328,k1_zfmisc_1(A_327))
      | v1_xboole_0(A_328) ) ),
    inference(resolution,[status(thm)],[c_3979,c_2])).

tff(c_4022,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_4004])).

tff(c_4031,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3772,c_4022])).

tff(c_4033,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3911,c_4031])).

tff(c_4035,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_3910])).

tff(c_3779,plain,(
    ! [A_48] :
      ( A_48 = '#skF_3'
      | ~ v1_xboole_0(A_48) ) ),
    inference(resolution,[status(thm)],[c_3772,c_170])).

tff(c_4038,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4035,c_3779])).

tff(c_4044,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3786,c_4038])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:33:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.15/2.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.23/2.23  
% 5.23/2.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.23/2.23  %$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 5.23/2.23  
% 5.23/2.23  %Foreground sorts:
% 5.23/2.23  
% 5.23/2.23  
% 5.23/2.23  %Background operators:
% 5.23/2.23  
% 5.23/2.23  
% 5.23/2.23  %Foreground operators:
% 5.23/2.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.23/2.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.23/2.23  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.23/2.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.23/2.23  tff('#skF_5', type, '#skF_5': $i).
% 5.23/2.23  tff('#skF_3', type, '#skF_3': $i).
% 5.23/2.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.23/2.23  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 5.23/2.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.23/2.23  tff('#skF_4', type, '#skF_4': $i).
% 5.23/2.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.23/2.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.23/2.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.23/2.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.23/2.23  
% 5.23/2.25  tff(f_85, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_subset_1)).
% 5.23/2.25  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 5.23/2.25  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.23/2.25  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 5.23/2.25  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.23/2.25  tff(f_45, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 5.23/2.26  tff(f_50, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_xboole_1)).
% 5.23/2.26  tff(c_30, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.23/2.26  tff(c_24, plain, (![B_15, A_14]: (m1_subset_1(B_15, A_14) | ~v1_xboole_0(B_15) | ~v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.23/2.26  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.23/2.26  tff(c_117, plain, (![D_47]: (r2_hidden(D_47, '#skF_4') | ~r2_hidden(D_47, '#skF_5') | ~m1_subset_1(D_47, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.23/2.26  tff(c_131, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_5'), '#skF_3') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_117])).
% 5.23/2.26  tff(c_3333, plain, (~m1_subset_1('#skF_1'('#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_131])).
% 5.23/2.26  tff(c_3340, plain, (~v1_xboole_0('#skF_1'('#skF_5')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_24, c_3333])).
% 5.23/2.26  tff(c_3347, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_3340])).
% 5.23/2.26  tff(c_68, plain, (![B_38, A_39]: (m1_subset_1(B_38, A_39) | ~r2_hidden(B_38, A_39) | v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.23/2.26  tff(c_76, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_68])).
% 5.23/2.26  tff(c_22, plain, (![B_15, A_14]: (r2_hidden(B_15, A_14) | ~m1_subset_1(B_15, A_14) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.23/2.26  tff(c_57, plain, (![D_35]: (r2_hidden(D_35, '#skF_5') | ~r2_hidden(D_35, '#skF_4') | ~m1_subset_1(D_35, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.23/2.26  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.23/2.26  tff(c_61, plain, (![D_35]: (~v1_xboole_0('#skF_5') | ~r2_hidden(D_35, '#skF_4') | ~m1_subset_1(D_35, '#skF_3'))), inference(resolution, [status(thm)], [c_57, c_2])).
% 5.23/2.26  tff(c_187, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_61])).
% 5.23/2.26  tff(c_188, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_187, c_131])).
% 5.23/2.26  tff(c_189, plain, (~m1_subset_1('#skF_1'('#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_188])).
% 5.23/2.26  tff(c_193, plain, (~v1_xboole_0('#skF_1'('#skF_5')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_24, c_189])).
% 5.23/2.26  tff(c_194, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_193])).
% 5.23/2.26  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.23/2.26  tff(c_221, plain, (![C_66, A_67, B_68]: (r2_hidden(C_66, A_67) | ~r2_hidden(C_66, B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.23/2.26  tff(c_479, plain, (![B_94, A_95, A_96]: (r2_hidden(B_94, A_95) | ~m1_subset_1(A_96, k1_zfmisc_1(A_95)) | ~m1_subset_1(B_94, A_96) | v1_xboole_0(A_96))), inference(resolution, [status(thm)], [c_22, c_221])).
% 5.23/2.26  tff(c_493, plain, (![B_94]: (r2_hidden(B_94, '#skF_3') | ~m1_subset_1(B_94, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_32, c_479])).
% 5.23/2.26  tff(c_506, plain, (![B_97]: (r2_hidden(B_97, '#skF_3') | ~m1_subset_1(B_97, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_187, c_493])).
% 5.23/2.26  tff(c_20, plain, (![B_15, A_14]: (m1_subset_1(B_15, A_14) | ~r2_hidden(B_15, A_14) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.23/2.26  tff(c_517, plain, (![B_97]: (m1_subset_1(B_97, '#skF_3') | v1_xboole_0('#skF_3') | ~m1_subset_1(B_97, '#skF_5'))), inference(resolution, [status(thm)], [c_506, c_20])).
% 5.23/2.26  tff(c_550, plain, (![B_99]: (m1_subset_1(B_99, '#skF_3') | ~m1_subset_1(B_99, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_194, c_517])).
% 5.23/2.26  tff(c_565, plain, (m1_subset_1('#skF_1'('#skF_5'), '#skF_3') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_76, c_550])).
% 5.23/2.26  tff(c_580, plain, $false, inference(negUnitSimplification, [status(thm)], [c_187, c_189, c_565])).
% 5.23/2.26  tff(c_582, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_193])).
% 5.23/2.26  tff(c_640, plain, (![C_106, A_107, B_108]: (r2_hidden(C_106, A_107) | ~r2_hidden(C_106, B_108) | ~m1_subset_1(B_108, k1_zfmisc_1(A_107)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.23/2.26  tff(c_662, plain, (![A_111, A_112]: (r2_hidden('#skF_1'(A_111), A_112) | ~m1_subset_1(A_111, k1_zfmisc_1(A_112)) | v1_xboole_0(A_111))), inference(resolution, [status(thm)], [c_4, c_640])).
% 5.23/2.26  tff(c_687, plain, (![A_113, A_114]: (~v1_xboole_0(A_113) | ~m1_subset_1(A_114, k1_zfmisc_1(A_113)) | v1_xboole_0(A_114))), inference(resolution, [status(thm)], [c_662, c_2])).
% 5.23/2.26  tff(c_698, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_32, c_687])).
% 5.23/2.26  tff(c_706, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_582, c_698])).
% 5.23/2.26  tff(c_708, plain, $false, inference(negUnitSimplification, [status(thm)], [c_187, c_706])).
% 5.23/2.26  tff(c_709, plain, (r2_hidden('#skF_1'('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_188])).
% 5.23/2.26  tff(c_742, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_709, c_2])).
% 5.23/2.26  tff(c_132, plain, (![A_48, B_49]: (r2_hidden('#skF_2'(A_48, B_49), A_48) | r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.23/2.26  tff(c_149, plain, (![A_48, B_49]: (m1_subset_1('#skF_2'(A_48, B_49), A_48) | v1_xboole_0(A_48) | r1_tarski(A_48, B_49))), inference(resolution, [status(thm)], [c_132, c_20])).
% 5.23/2.26  tff(c_710, plain, (m1_subset_1('#skF_1'('#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_188])).
% 5.23/2.26  tff(c_26, plain, (![B_15, A_14]: (v1_xboole_0(B_15) | ~m1_subset_1(B_15, A_14) | ~v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.23/2.26  tff(c_746, plain, (v1_xboole_0('#skF_1'('#skF_5')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_710, c_26])).
% 5.23/2.26  tff(c_747, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_746])).
% 5.23/2.26  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.23/2.26  tff(c_748, plain, (![C_116, A_117, B_118]: (r2_hidden(C_116, A_117) | ~r2_hidden(C_116, B_118) | ~m1_subset_1(B_118, k1_zfmisc_1(A_117)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.23/2.26  tff(c_1670, plain, (![B_188, A_189, A_190]: (r2_hidden(B_188, A_189) | ~m1_subset_1(A_190, k1_zfmisc_1(A_189)) | ~m1_subset_1(B_188, A_190) | v1_xboole_0(A_190))), inference(resolution, [status(thm)], [c_22, c_748])).
% 5.23/2.26  tff(c_1692, plain, (![B_188]: (r2_hidden(B_188, '#skF_3') | ~m1_subset_1(B_188, '#skF_4') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_1670])).
% 5.23/2.26  tff(c_1727, plain, (![B_192]: (r2_hidden(B_192, '#skF_3') | ~m1_subset_1(B_192, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_742, c_1692])).
% 5.23/2.26  tff(c_1738, plain, (![B_192]: (m1_subset_1(B_192, '#skF_3') | v1_xboole_0('#skF_3') | ~m1_subset_1(B_192, '#skF_4'))), inference(resolution, [status(thm)], [c_1727, c_20])).
% 5.23/2.26  tff(c_1747, plain, (![B_192]: (m1_subset_1(B_192, '#skF_3') | ~m1_subset_1(B_192, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_747, c_1738])).
% 5.23/2.26  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.23/2.26  tff(c_38, plain, (![D_24]: (r2_hidden(D_24, '#skF_5') | ~r2_hidden(D_24, '#skF_4') | ~m1_subset_1(D_24, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.23/2.26  tff(c_106, plain, (![A_45, B_46]: (~r2_hidden('#skF_2'(A_45, B_46), B_46) | r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.23/2.26  tff(c_2051, plain, (![A_205]: (r1_tarski(A_205, '#skF_5') | ~r2_hidden('#skF_2'(A_205, '#skF_5'), '#skF_4') | ~m1_subset_1('#skF_2'(A_205, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_38, c_106])).
% 5.23/2.26  tff(c_2079, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_5'), '#skF_3') | r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_10, c_2051])).
% 5.23/2.26  tff(c_2083, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_2079])).
% 5.23/2.26  tff(c_2090, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_1747, c_2083])).
% 5.23/2.26  tff(c_2094, plain, (v1_xboole_0('#skF_4') | r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_149, c_2090])).
% 5.23/2.26  tff(c_2100, plain, (r1_tarski('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_742, c_2094])).
% 5.23/2.26  tff(c_91, plain, (![A_43, B_44]: (r2_xboole_0(A_43, B_44) | B_44=A_43 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.23/2.26  tff(c_18, plain, (![B_13, A_12]: (~r2_xboole_0(B_13, A_12) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.23/2.26  tff(c_102, plain, (![B_44, A_43]: (~r1_tarski(B_44, A_43) | B_44=A_43 | ~r1_tarski(A_43, B_44))), inference(resolution, [status(thm)], [c_91, c_18])).
% 5.23/2.26  tff(c_2142, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_2100, c_102])).
% 5.23/2.26  tff(c_2158, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_30, c_2142])).
% 5.23/2.26  tff(c_1690, plain, (![B_188]: (r2_hidden(B_188, '#skF_3') | ~m1_subset_1(B_188, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_32, c_1670])).
% 5.23/2.26  tff(c_1705, plain, (![B_191]: (r2_hidden(B_191, '#skF_3') | ~m1_subset_1(B_191, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_187, c_1690])).
% 5.23/2.26  tff(c_1716, plain, (![B_191]: (m1_subset_1(B_191, '#skF_3') | v1_xboole_0('#skF_3') | ~m1_subset_1(B_191, '#skF_5'))), inference(resolution, [status(thm)], [c_1705, c_20])).
% 5.23/2.26  tff(c_1749, plain, (![B_193]: (m1_subset_1(B_193, '#skF_3') | ~m1_subset_1(B_193, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_747, c_1716])).
% 5.23/2.26  tff(c_1768, plain, (![B_49]: (m1_subset_1('#skF_2'('#skF_5', B_49), '#skF_3') | v1_xboole_0('#skF_5') | r1_tarski('#skF_5', B_49))), inference(resolution, [status(thm)], [c_149, c_1749])).
% 5.23/2.26  tff(c_2336, plain, (![B_215]: (m1_subset_1('#skF_2'('#skF_5', B_215), '#skF_3') | r1_tarski('#skF_5', B_215))), inference(negUnitSimplification, [status(thm)], [c_187, c_1768])).
% 5.23/2.26  tff(c_36, plain, (![D_24]: (r2_hidden(D_24, '#skF_4') | ~r2_hidden(D_24, '#skF_5') | ~m1_subset_1(D_24, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.23/2.26  tff(c_1615, plain, (![B_180]: (r2_hidden('#skF_2'('#skF_5', B_180), '#skF_4') | ~m1_subset_1('#skF_2'('#skF_5', B_180), '#skF_3') | r1_tarski('#skF_5', B_180))), inference(resolution, [status(thm)], [c_132, c_36])).
% 5.23/2.26  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.23/2.26  tff(c_1639, plain, (~m1_subset_1('#skF_2'('#skF_5', '#skF_4'), '#skF_3') | r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1615, c_8])).
% 5.23/2.26  tff(c_1644, plain, (~m1_subset_1('#skF_2'('#skF_5', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1639])).
% 5.23/2.26  tff(c_2339, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_2336, c_1644])).
% 5.23/2.26  tff(c_2350, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2158, c_2339])).
% 5.23/2.26  tff(c_2351, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_2079])).
% 5.23/2.26  tff(c_2371, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_2351, c_102])).
% 5.23/2.26  tff(c_2387, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_30, c_2371])).
% 5.23/2.26  tff(c_2558, plain, (![B_224]: (m1_subset_1('#skF_2'('#skF_5', B_224), '#skF_3') | r1_tarski('#skF_5', B_224))), inference(negUnitSimplification, [status(thm)], [c_187, c_1768])).
% 5.23/2.26  tff(c_2561, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_2558, c_1644])).
% 5.23/2.26  tff(c_2572, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2387, c_2561])).
% 5.23/2.26  tff(c_2573, plain, (r1_tarski('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_1639])).
% 5.23/2.26  tff(c_2587, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_2573, c_102])).
% 5.23/2.26  tff(c_2596, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_30, c_2587])).
% 5.23/2.26  tff(c_2802, plain, (![B_239, A_240, A_241]: (r2_hidden(B_239, A_240) | ~m1_subset_1(A_241, k1_zfmisc_1(A_240)) | ~m1_subset_1(B_239, A_241) | v1_xboole_0(A_241))), inference(resolution, [status(thm)], [c_22, c_748])).
% 5.23/2.26  tff(c_2824, plain, (![B_239]: (r2_hidden(B_239, '#skF_3') | ~m1_subset_1(B_239, '#skF_4') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_2802])).
% 5.23/2.26  tff(c_2859, plain, (![B_243]: (r2_hidden(B_243, '#skF_3') | ~m1_subset_1(B_243, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_742, c_2824])).
% 5.23/2.26  tff(c_2870, plain, (![B_243]: (m1_subset_1(B_243, '#skF_3') | v1_xboole_0('#skF_3') | ~m1_subset_1(B_243, '#skF_4'))), inference(resolution, [status(thm)], [c_2859, c_20])).
% 5.23/2.26  tff(c_2972, plain, (![B_246]: (m1_subset_1(B_246, '#skF_3') | ~m1_subset_1(B_246, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_747, c_2870])).
% 5.23/2.26  tff(c_2933, plain, (![A_245]: (r1_tarski(A_245, '#skF_5') | ~r2_hidden('#skF_2'(A_245, '#skF_5'), '#skF_4') | ~m1_subset_1('#skF_2'(A_245, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_38, c_106])).
% 5.23/2.26  tff(c_2951, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_5'), '#skF_3') | r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_10, c_2933])).
% 5.23/2.26  tff(c_2964, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_2596, c_2596, c_2951])).
% 5.23/2.26  tff(c_2983, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_2972, c_2964])).
% 5.23/2.26  tff(c_2990, plain, (v1_xboole_0('#skF_4') | r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_149, c_2983])).
% 5.23/2.26  tff(c_2997, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2596, c_742, c_2990])).
% 5.23/2.26  tff(c_2999, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_746])).
% 5.23/2.26  tff(c_2998, plain, (v1_xboole_0('#skF_1'('#skF_5'))), inference(splitRight, [status(thm)], [c_746])).
% 5.23/2.26  tff(c_150, plain, (![A_48, B_49]: (~v1_xboole_0(A_48) | r1_tarski(A_48, B_49))), inference(resolution, [status(thm)], [c_132, c_2])).
% 5.23/2.26  tff(c_153, plain, (![B_53, A_54]: (~r1_tarski(B_53, A_54) | B_53=A_54 | ~r1_tarski(A_54, B_53))), inference(resolution, [status(thm)], [c_91, c_18])).
% 5.23/2.26  tff(c_163, plain, (![B_55, A_56]: (B_55=A_56 | ~r1_tarski(B_55, A_56) | ~v1_xboole_0(A_56))), inference(resolution, [status(thm)], [c_150, c_153])).
% 5.23/2.26  tff(c_170, plain, (![B_49, A_48]: (B_49=A_48 | ~v1_xboole_0(B_49) | ~v1_xboole_0(A_48))), inference(resolution, [status(thm)], [c_150, c_163])).
% 5.23/2.26  tff(c_3022, plain, (![A_250]: (A_250='#skF_3' | ~v1_xboole_0(A_250))), inference(resolution, [status(thm)], [c_2999, c_170])).
% 5.23/2.26  tff(c_3029, plain, ('#skF_1'('#skF_5')='#skF_3'), inference(resolution, [status(thm)], [c_2998, c_3022])).
% 5.23/2.26  tff(c_3034, plain, (r2_hidden('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3029, c_709])).
% 5.23/2.26  tff(c_28, plain, (![C_19, A_16, B_17]: (r2_hidden(C_19, A_16) | ~r2_hidden(C_19, B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.23/2.26  tff(c_3304, plain, (![A_264]: (r2_hidden('#skF_3', A_264) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_264)))), inference(resolution, [status(thm)], [c_3034, c_28])).
% 5.23/2.26  tff(c_3312, plain, (r2_hidden('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_3304])).
% 5.23/2.26  tff(c_3322, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_3312, c_2])).
% 5.23/2.26  tff(c_3330, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2999, c_3322])).
% 5.23/2.26  tff(c_3361, plain, (![D_269]: (~r2_hidden(D_269, '#skF_4') | ~m1_subset_1(D_269, '#skF_3'))), inference(splitRight, [status(thm)], [c_61])).
% 5.23/2.26  tff(c_3375, plain, (![B_15]: (~m1_subset_1(B_15, '#skF_3') | ~m1_subset_1(B_15, '#skF_4') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_22, c_3361])).
% 5.23/2.26  tff(c_3389, plain, (![B_271]: (~m1_subset_1(B_271, '#skF_3') | ~m1_subset_1(B_271, '#skF_4'))), inference(splitLeft, [status(thm)], [c_3375])).
% 5.23/2.26  tff(c_3393, plain, (~m1_subset_1('#skF_1'('#skF_3'), '#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_76, c_3389])).
% 5.23/2.26  tff(c_3400, plain, (~m1_subset_1('#skF_1'('#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_3347, c_3393])).
% 5.23/2.26  tff(c_3405, plain, (~v1_xboole_0('#skF_1'('#skF_3')) | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_24, c_3400])).
% 5.23/2.26  tff(c_3406, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_3405])).
% 5.23/2.26  tff(c_3348, plain, (![C_266, A_267, B_268]: (r2_hidden(C_266, A_267) | ~r2_hidden(C_266, B_268) | ~m1_subset_1(B_268, k1_zfmisc_1(A_267)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.23/2.26  tff(c_3649, plain, (![B_299, A_300, A_301]: (r2_hidden(B_299, A_300) | ~m1_subset_1(A_301, k1_zfmisc_1(A_300)) | ~m1_subset_1(B_299, A_301) | v1_xboole_0(A_301))), inference(resolution, [status(thm)], [c_22, c_3348])).
% 5.23/2.26  tff(c_3662, plain, (![B_299]: (r2_hidden(B_299, '#skF_3') | ~m1_subset_1(B_299, '#skF_4') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_3649])).
% 5.23/2.26  tff(c_3671, plain, (![B_302]: (r2_hidden(B_302, '#skF_3') | ~m1_subset_1(B_302, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_3406, c_3662])).
% 5.23/2.26  tff(c_3682, plain, (![B_302]: (m1_subset_1(B_302, '#skF_3') | v1_xboole_0('#skF_3') | ~m1_subset_1(B_302, '#skF_4'))), inference(resolution, [status(thm)], [c_3671, c_20])).
% 5.23/2.26  tff(c_3693, plain, (![B_303]: (m1_subset_1(B_303, '#skF_3') | ~m1_subset_1(B_303, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_3347, c_3682])).
% 5.23/2.26  tff(c_3388, plain, (![B_15]: (~m1_subset_1(B_15, '#skF_3') | ~m1_subset_1(B_15, '#skF_4'))), inference(splitLeft, [status(thm)], [c_3375])).
% 5.23/2.26  tff(c_3729, plain, (![B_304]: (~m1_subset_1(B_304, '#skF_4'))), inference(resolution, [status(thm)], [c_3693, c_3388])).
% 5.23/2.26  tff(c_3737, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_76, c_3729])).
% 5.23/2.26  tff(c_3748, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3406, c_3737])).
% 5.23/2.26  tff(c_3750, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_3405])).
% 5.23/2.26  tff(c_3332, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_61])).
% 5.23/2.26  tff(c_3336, plain, (![A_48]: (A_48='#skF_5' | ~v1_xboole_0(A_48))), inference(resolution, [status(thm)], [c_3332, c_170])).
% 5.23/2.26  tff(c_3754, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_3750, c_3336])).
% 5.23/2.26  tff(c_3760, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_3754])).
% 5.23/2.26  tff(c_3761, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_3375])).
% 5.23/2.26  tff(c_3764, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_3761, c_3336])).
% 5.23/2.26  tff(c_3770, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_3764])).
% 5.23/2.26  tff(c_3772, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_3340])).
% 5.23/2.26  tff(c_3778, plain, ('#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_3772, c_3336])).
% 5.23/2.26  tff(c_3786, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3778, c_30])).
% 5.23/2.26  tff(c_3825, plain, (![D_309]: (~r2_hidden(D_309, '#skF_4') | ~m1_subset_1(D_309, '#skF_3'))), inference(splitRight, [status(thm)], [c_61])).
% 5.23/2.26  tff(c_3839, plain, (![B_15]: (~m1_subset_1(B_15, '#skF_3') | ~m1_subset_1(B_15, '#skF_4') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_22, c_3825])).
% 5.23/2.26  tff(c_3886, plain, (![B_316]: (~m1_subset_1(B_316, '#skF_3') | ~m1_subset_1(B_316, '#skF_4'))), inference(splitLeft, [status(thm)], [c_3839])).
% 5.23/2.26  tff(c_3894, plain, (![B_15]: (~m1_subset_1(B_15, '#skF_4') | ~v1_xboole_0(B_15) | ~v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_3886])).
% 5.23/2.26  tff(c_3900, plain, (![B_317]: (~m1_subset_1(B_317, '#skF_4') | ~v1_xboole_0(B_317))), inference(demodulation, [status(thm), theory('equality')], [c_3772, c_3894])).
% 5.23/2.26  tff(c_3910, plain, (![B_15]: (~v1_xboole_0(B_15) | ~v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_3900])).
% 5.23/2.26  tff(c_3911, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_3910])).
% 5.23/2.26  tff(c_3792, plain, (![C_305, A_306, B_307]: (r2_hidden(C_305, A_306) | ~r2_hidden(C_305, B_307) | ~m1_subset_1(B_307, k1_zfmisc_1(A_306)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.23/2.26  tff(c_3979, plain, (![A_325, A_326]: (r2_hidden('#skF_1'(A_325), A_326) | ~m1_subset_1(A_325, k1_zfmisc_1(A_326)) | v1_xboole_0(A_325))), inference(resolution, [status(thm)], [c_4, c_3792])).
% 5.23/2.26  tff(c_4004, plain, (![A_327, A_328]: (~v1_xboole_0(A_327) | ~m1_subset_1(A_328, k1_zfmisc_1(A_327)) | v1_xboole_0(A_328))), inference(resolution, [status(thm)], [c_3979, c_2])).
% 5.23/2.26  tff(c_4022, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_34, c_4004])).
% 5.23/2.26  tff(c_4031, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3772, c_4022])).
% 5.23/2.26  tff(c_4033, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3911, c_4031])).
% 5.23/2.26  tff(c_4035, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_3910])).
% 5.23/2.26  tff(c_3779, plain, (![A_48]: (A_48='#skF_3' | ~v1_xboole_0(A_48))), inference(resolution, [status(thm)], [c_3772, c_170])).
% 5.23/2.26  tff(c_4038, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_4035, c_3779])).
% 5.23/2.26  tff(c_4044, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3786, c_4038])).
% 5.23/2.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.23/2.26  
% 5.23/2.26  Inference rules
% 5.23/2.26  ----------------------
% 5.23/2.26  #Ref     : 0
% 5.23/2.26  #Sup     : 848
% 5.23/2.26  #Fact    : 0
% 5.23/2.26  #Define  : 0
% 5.23/2.26  #Split   : 22
% 5.23/2.26  #Chain   : 0
% 5.23/2.26  #Close   : 0
% 5.23/2.26  
% 5.23/2.26  Ordering : KBO
% 5.23/2.26  
% 5.23/2.26  Simplification rules
% 5.23/2.26  ----------------------
% 5.23/2.26  #Subsume      : 211
% 5.23/2.26  #Demod        : 169
% 5.23/2.26  #Tautology    : 144
% 5.23/2.26  #SimpNegUnit  : 143
% 5.23/2.26  #BackRed      : 10
% 5.23/2.26  
% 5.23/2.26  #Partial instantiations: 0
% 5.23/2.26  #Strategies tried      : 1
% 5.23/2.26  
% 5.23/2.26  Timing (in seconds)
% 5.23/2.26  ----------------------
% 5.23/2.26  Preprocessing        : 0.41
% 5.23/2.26  Parsing              : 0.24
% 5.23/2.26  CNF conversion       : 0.03
% 5.23/2.26  Main loop            : 0.87
% 5.23/2.26  Inferencing          : 0.31
% 5.23/2.26  Reduction            : 0.24
% 5.23/2.26  Demodulation         : 0.15
% 5.23/2.26  BG Simplification    : 0.03
% 5.23/2.26  Subsumption          : 0.22
% 5.23/2.26  Abstraction          : 0.04
% 5.23/2.26  MUC search           : 0.00
% 5.23/2.26  Cooper               : 0.00
% 5.23/2.26  Total                : 1.35
% 5.23/2.26  Index Insertion      : 0.00
% 5.23/2.26  Index Deletion       : 0.00
% 5.23/2.26  Index Matching       : 0.00
% 5.23/2.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
