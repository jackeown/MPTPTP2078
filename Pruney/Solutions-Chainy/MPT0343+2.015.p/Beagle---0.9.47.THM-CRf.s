%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:19 EST 2020

% Result     : Theorem 5.48s
% Output     : CNFRefutation 5.67s
% Verified   : 
% Statistics : Number of formulae       :  205 ( 965 expanded)
%              Number of leaves         :   21 ( 305 expanded)
%              Depth                    :   19
%              Number of atoms          :  438 (2923 expanded)
%              Number of equality atoms :   21 ( 147 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
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

tff(f_47,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_30,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_57,plain,(
    ! [D_35] :
      ( r2_hidden(D_35,'#skF_5')
      | ~ r2_hidden(D_35,'#skF_4')
      | ~ m1_subset_1(D_35,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( ~ v1_xboole_0(B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_61,plain,(
    ! [D_35] :
      ( ~ v1_xboole_0('#skF_5')
      | ~ r2_hidden(D_35,'#skF_4')
      | ~ m1_subset_1(D_35,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_57,c_12])).

tff(c_133,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_61])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( r2_hidden(B_9,A_8)
      | ~ m1_subset_1(B_9,A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_118,plain,(
    ! [D_50] :
      ( r2_hidden(D_50,'#skF_4')
      | ~ r2_hidden(D_50,'#skF_5')
      | ~ m1_subset_1(D_50,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_130,plain,(
    ! [B_9] :
      ( r2_hidden(B_9,'#skF_4')
      | ~ m1_subset_1(B_9,'#skF_3')
      | ~ m1_subset_1(B_9,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_16,c_118])).

tff(c_178,plain,(
    ! [B_61] :
      ( r2_hidden(B_61,'#skF_4')
      | ~ m1_subset_1(B_61,'#skF_3')
      | ~ m1_subset_1(B_61,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_130])).

tff(c_194,plain,(
    ! [B_61] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ m1_subset_1(B_61,'#skF_3')
      | ~ m1_subset_1(B_61,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_178,c_12])).

tff(c_195,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_194])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_xboole_0(A_1,B_2)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | ~ r2_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_38,plain,(
    ! [D_25] :
      ( r2_hidden(D_25,'#skF_5')
      | ~ r2_hidden(D_25,'#skF_4')
      | ~ m1_subset_1(D_25,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_102,plain,(
    ! [A_48,B_49] :
      ( ~ r2_hidden('#skF_1'(A_48,B_49),A_48)
      | ~ r2_xboole_0(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_509,plain,(
    ! [B_87] :
      ( ~ r2_xboole_0('#skF_5',B_87)
      | ~ r2_hidden('#skF_1'('#skF_5',B_87),'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_5',B_87),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_102])).

tff(c_534,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_5','#skF_4'),'#skF_3')
    | ~ r2_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_509])).

tff(c_561,plain,(
    ~ r2_xboole_0('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_534])).

tff(c_564,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_2,c_561])).

tff(c_567,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_564])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_28,plain,(
    ! [A_14,B_15,C_19] :
      ( m1_subset_1('#skF_2'(A_14,B_15,C_19),A_14)
      | r1_tarski(B_15,C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_160,plain,(
    ! [A_58,B_59,C_60] :
      ( r2_hidden('#skF_2'(A_58,B_59,C_60),B_59)
      | r1_tarski(B_59,C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(A_58))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_36,plain,(
    ! [D_25] :
      ( r2_hidden(D_25,'#skF_4')
      | ~ r2_hidden(D_25,'#skF_5')
      | ~ m1_subset_1(D_25,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1025,plain,(
    ! [A_132,C_133] :
      ( r2_hidden('#skF_2'(A_132,'#skF_5',C_133),'#skF_4')
      | ~ m1_subset_1('#skF_2'(A_132,'#skF_5',C_133),'#skF_3')
      | r1_tarski('#skF_5',C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(A_132))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_132)) ) ),
    inference(resolution,[status(thm)],[c_160,c_36])).

tff(c_24,plain,(
    ! [A_14,B_15,C_19] :
      ( ~ r2_hidden('#skF_2'(A_14,B_15,C_19),C_19)
      | r1_tarski(B_15,C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1029,plain,(
    ! [A_132] :
      ( ~ m1_subset_1('#skF_2'(A_132,'#skF_5','#skF_4'),'#skF_3')
      | r1_tarski('#skF_5','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_132))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_132)) ) ),
    inference(resolution,[status(thm)],[c_1025,c_24])).

tff(c_1694,plain,(
    ! [A_168] :
      ( ~ m1_subset_1('#skF_2'(A_168,'#skF_5','#skF_4'),'#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_168))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_168)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_567,c_567,c_1029])).

tff(c_1701,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_1694])).

tff(c_1708,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_1701])).

tff(c_1710,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_567,c_1708])).

tff(c_1712,plain,(
    r2_xboole_0('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_534])).

tff(c_67,plain,(
    ! [A_38,B_39] :
      ( r2_hidden('#skF_1'(A_38,B_39),B_39)
      | ~ r2_xboole_0(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( m1_subset_1(B_9,A_8)
      | ~ r2_hidden(B_9,A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_74,plain,(
    ! [A_38,B_39] :
      ( m1_subset_1('#skF_1'(A_38,B_39),B_39)
      | v1_xboole_0(B_39)
      | ~ r2_xboole_0(A_38,B_39) ) ),
    inference(resolution,[status(thm)],[c_67,c_14])).

tff(c_134,plain,(
    ! [C_51,A_52,B_53] :
      ( r2_hidden(C_51,A_52)
      | ~ r2_hidden(C_51,B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_249,plain,(
    ! [B_65,A_66,A_67] :
      ( r2_hidden(B_65,A_66)
      | ~ m1_subset_1(A_67,k1_zfmisc_1(A_66))
      | ~ m1_subset_1(B_65,A_67)
      | v1_xboole_0(A_67) ) ),
    inference(resolution,[status(thm)],[c_16,c_134])).

tff(c_257,plain,(
    ! [B_65] :
      ( r2_hidden(B_65,'#skF_3')
      | ~ m1_subset_1(B_65,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_32,c_249])).

tff(c_268,plain,(
    ! [B_68] :
      ( r2_hidden(B_68,'#skF_3')
      | ~ m1_subset_1(B_68,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_257])).

tff(c_284,plain,(
    ! [B_68] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ m1_subset_1(B_68,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_268,c_12])).

tff(c_285,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_284])).

tff(c_259,plain,(
    ! [B_65] :
      ( r2_hidden(B_65,'#skF_3')
      | ~ m1_subset_1(B_65,'#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_249])).

tff(c_300,plain,(
    ! [B_72] :
      ( r2_hidden(B_72,'#skF_3')
      | ~ m1_subset_1(B_72,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_259])).

tff(c_309,plain,(
    ! [B_72] :
      ( m1_subset_1(B_72,'#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(B_72,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_300,c_14])).

tff(c_317,plain,(
    ! [B_72] :
      ( m1_subset_1(B_72,'#skF_3')
      | ~ m1_subset_1(B_72,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_285,c_309])).

tff(c_1711,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_534])).

tff(c_1732,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_317,c_1711])).

tff(c_1744,plain,
    ( v1_xboole_0('#skF_4')
    | ~ r2_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_1732])).

tff(c_1750,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1712,c_1744])).

tff(c_1752,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_1750])).

tff(c_1754,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_284])).

tff(c_1777,plain,(
    ! [A_174,B_175,C_176] :
      ( m1_subset_1('#skF_2'(A_174,B_175,C_176),A_174)
      | r1_tarski(B_175,C_176)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(A_174))
      | ~ m1_subset_1(B_175,k1_zfmisc_1(A_174)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_20,plain,(
    ! [B_9,A_8] :
      ( v1_xboole_0(B_9)
      | ~ m1_subset_1(B_9,A_8)
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2210,plain,(
    ! [A_222,B_223,C_224] :
      ( v1_xboole_0('#skF_2'(A_222,B_223,C_224))
      | ~ v1_xboole_0(A_222)
      | r1_tarski(B_223,C_224)
      | ~ m1_subset_1(C_224,k1_zfmisc_1(A_222))
      | ~ m1_subset_1(B_223,k1_zfmisc_1(A_222)) ) ),
    inference(resolution,[status(thm)],[c_1777,c_20])).

tff(c_2223,plain,(
    ! [B_223] :
      ( v1_xboole_0('#skF_2'('#skF_3',B_223,'#skF_4'))
      | ~ v1_xboole_0('#skF_3')
      | r1_tarski(B_223,'#skF_4')
      | ~ m1_subset_1(B_223,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_34,c_2210])).

tff(c_2298,plain,(
    ! [B_228] :
      ( v1_xboole_0('#skF_2'('#skF_3',B_228,'#skF_4'))
      | r1_tarski(B_228,'#skF_4')
      | ~ m1_subset_1(B_228,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1754,c_2223])).

tff(c_2322,plain,
    ( v1_xboole_0('#skF_2'('#skF_3','#skF_5','#skF_4'))
    | r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_2298])).

tff(c_2325,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2322])).

tff(c_1809,plain,(
    ! [B_178] :
      ( r2_hidden(B_178,'#skF_3')
      | ~ m1_subset_1(B_178,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_259])).

tff(c_1821,plain,(
    ! [B_178] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ m1_subset_1(B_178,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1809,c_12])).

tff(c_1829,plain,(
    ! [B_179] : ~ m1_subset_1(B_179,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1754,c_1821])).

tff(c_1837,plain,(
    ! [A_38] :
      ( v1_xboole_0('#skF_4')
      | ~ r2_xboole_0(A_38,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_74,c_1829])).

tff(c_1847,plain,(
    ! [A_180] : ~ r2_xboole_0(A_180,'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_1837])).

tff(c_1852,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ r1_tarski(A_1,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2,c_1847])).

tff(c_2328,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2325,c_1852])).

tff(c_2335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_2328])).

tff(c_2337,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_2322])).

tff(c_2275,plain,(
    ! [A_226,C_227] :
      ( r2_hidden('#skF_2'(A_226,'#skF_5',C_227),'#skF_4')
      | ~ m1_subset_1('#skF_2'(A_226,'#skF_5',C_227),'#skF_3')
      | r1_tarski('#skF_5',C_227)
      | ~ m1_subset_1(C_227,k1_zfmisc_1(A_226))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_226)) ) ),
    inference(resolution,[status(thm)],[c_160,c_36])).

tff(c_2291,plain,(
    ! [A_226] :
      ( ~ m1_subset_1('#skF_2'(A_226,'#skF_5','#skF_4'),'#skF_3')
      | r1_tarski('#skF_5','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_226))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_226)) ) ),
    inference(resolution,[status(thm)],[c_2275,c_24])).

tff(c_2350,plain,(
    ! [A_232] :
      ( ~ m1_subset_1('#skF_2'(A_232,'#skF_5','#skF_4'),'#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_232))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_232)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2337,c_2291])).

tff(c_2354,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_2350])).

tff(c_2360,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_2354])).

tff(c_2362,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2337,c_2360])).

tff(c_2364,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_3074,plain,(
    ! [B_308,C_309,A_310] :
      ( ~ v1_xboole_0(B_308)
      | r1_tarski(B_308,C_309)
      | ~ m1_subset_1(C_309,k1_zfmisc_1(A_310))
      | ~ m1_subset_1(B_308,k1_zfmisc_1(A_310)) ) ),
    inference(resolution,[status(thm)],[c_160,c_12])).

tff(c_3095,plain,(
    ! [B_311] :
      ( ~ v1_xboole_0(B_311)
      | r1_tarski(B_311,'#skF_5')
      | ~ m1_subset_1(B_311,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_32,c_3074])).

tff(c_3113,plain,
    ( ~ v1_xboole_0('#skF_4')
    | r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_3095])).

tff(c_3123,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2364,c_3113])).

tff(c_2673,plain,(
    ! [B_263,C_264,A_265] :
      ( ~ v1_xboole_0(B_263)
      | r1_tarski(B_263,C_264)
      | ~ m1_subset_1(C_264,k1_zfmisc_1(A_265))
      | ~ m1_subset_1(B_263,k1_zfmisc_1(A_265)) ) ),
    inference(resolution,[status(thm)],[c_160,c_12])).

tff(c_2694,plain,(
    ! [B_266] :
      ( ~ v1_xboole_0(B_266)
      | r1_tarski(B_266,'#skF_5')
      | ~ m1_subset_1(B_266,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_32,c_2673])).

tff(c_2712,plain,
    ( ~ v1_xboole_0('#skF_4')
    | r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_2694])).

tff(c_2722,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2364,c_2712])).

tff(c_18,plain,(
    ! [B_9,A_8] :
      ( m1_subset_1(B_9,A_8)
      | ~ v1_xboole_0(B_9)
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2365,plain,(
    ! [B_233] :
      ( ~ m1_subset_1(B_233,'#skF_3')
      | ~ m1_subset_1(B_233,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_2369,plain,(
    ! [A_38] :
      ( ~ m1_subset_1('#skF_1'(A_38,'#skF_5'),'#skF_3')
      | v1_xboole_0('#skF_5')
      | ~ r2_xboole_0(A_38,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_74,c_2365])).

tff(c_2378,plain,(
    ! [A_234] :
      ( ~ m1_subset_1('#skF_1'(A_234,'#skF_5'),'#skF_3')
      | ~ r2_xboole_0(A_234,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_2369])).

tff(c_2382,plain,(
    ! [A_234] :
      ( ~ r2_xboole_0(A_234,'#skF_5')
      | ~ v1_xboole_0('#skF_1'(A_234,'#skF_5'))
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_18,c_2378])).

tff(c_2383,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2382])).

tff(c_2447,plain,(
    ! [B_242,A_243,A_244] :
      ( r2_hidden(B_242,A_243)
      | ~ m1_subset_1(A_244,k1_zfmisc_1(A_243))
      | ~ m1_subset_1(B_242,A_244)
      | v1_xboole_0(A_244) ) ),
    inference(resolution,[status(thm)],[c_16,c_134])).

tff(c_2455,plain,(
    ! [B_242] :
      ( r2_hidden(B_242,'#skF_3')
      | ~ m1_subset_1(B_242,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_32,c_2447])).

tff(c_2467,plain,(
    ! [B_245] :
      ( r2_hidden(B_245,'#skF_3')
      | ~ m1_subset_1(B_245,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_2455])).

tff(c_2480,plain,(
    ! [B_245] :
      ( m1_subset_1(B_245,'#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(B_245,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2467,c_14])).

tff(c_2509,plain,(
    ! [B_249] :
      ( m1_subset_1(B_249,'#skF_3')
      | ~ m1_subset_1(B_249,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_2383,c_2480])).

tff(c_2517,plain,(
    ! [A_38] :
      ( m1_subset_1('#skF_1'(A_38,'#skF_5'),'#skF_3')
      | v1_xboole_0('#skF_5')
      | ~ r2_xboole_0(A_38,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_74,c_2509])).

tff(c_2625,plain,(
    ! [A_257] :
      ( m1_subset_1('#skF_1'(A_257,'#skF_5'),'#skF_3')
      | ~ r2_xboole_0(A_257,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_2517])).

tff(c_2376,plain,(
    ! [A_38] :
      ( ~ m1_subset_1('#skF_1'(A_38,'#skF_5'),'#skF_3')
      | ~ r2_xboole_0(A_38,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_2369])).

tff(c_2640,plain,(
    ! [A_258] : ~ r2_xboole_0(A_258,'#skF_5') ),
    inference(resolution,[status(thm)],[c_2625,c_2376])).

tff(c_2645,plain,(
    ! [A_1] :
      ( A_1 = '#skF_5'
      | ~ r1_tarski(A_1,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2,c_2640])).

tff(c_2725,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2722,c_2645])).

tff(c_2732,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_2725])).

tff(c_2734,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2382])).

tff(c_2755,plain,(
    ! [B_269,A_270,A_271] :
      ( r2_hidden(B_269,A_270)
      | ~ m1_subset_1(A_271,k1_zfmisc_1(A_270))
      | ~ m1_subset_1(B_269,A_271)
      | v1_xboole_0(A_271) ) ),
    inference(resolution,[status(thm)],[c_16,c_134])).

tff(c_2763,plain,(
    ! [B_269] :
      ( r2_hidden(B_269,'#skF_3')
      | ~ m1_subset_1(B_269,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_32,c_2755])).

tff(c_2773,plain,(
    ! [B_272] :
      ( r2_hidden(B_272,'#skF_3')
      | ~ m1_subset_1(B_272,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_2763])).

tff(c_2785,plain,(
    ! [B_272] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ m1_subset_1(B_272,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2773,c_12])).

tff(c_2794,plain,(
    ! [B_273] : ~ m1_subset_1(B_273,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2734,c_2785])).

tff(c_2798,plain,(
    ! [A_38] :
      ( v1_xboole_0('#skF_5')
      | ~ r2_xboole_0(A_38,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_74,c_2794])).

tff(c_2823,plain,(
    ! [A_277] : ~ r2_xboole_0(A_277,'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_2798])).

tff(c_2828,plain,(
    ! [A_1] :
      ( A_1 = '#skF_5'
      | ~ r1_tarski(A_1,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2,c_2823])).

tff(c_3126,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3123,c_2828])).

tff(c_3133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_3126])).

tff(c_3135,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_4073,plain,(
    ! [A_422,B_423,C_424] :
      ( r2_hidden('#skF_2'(A_422,B_423,C_424),B_423)
      | r1_tarski(B_423,C_424)
      | ~ m1_subset_1(C_424,k1_zfmisc_1(A_422))
      | ~ m1_subset_1(B_423,k1_zfmisc_1(A_422)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4256,plain,(
    ! [B_446,C_447,A_448] :
      ( ~ v1_xboole_0(B_446)
      | r1_tarski(B_446,C_447)
      | ~ m1_subset_1(C_447,k1_zfmisc_1(A_448))
      | ~ m1_subset_1(B_446,k1_zfmisc_1(A_448)) ) ),
    inference(resolution,[status(thm)],[c_4073,c_12])).

tff(c_4305,plain,(
    ! [B_450] :
      ( ~ v1_xboole_0(B_450)
      | r1_tarski(B_450,'#skF_4')
      | ~ m1_subset_1(B_450,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_34,c_4256])).

tff(c_4320,plain,
    ( ~ v1_xboole_0('#skF_5')
    | r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_4305])).

tff(c_4331,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3135,c_4320])).

tff(c_3294,plain,(
    ! [A_334,B_335,C_336] :
      ( r2_hidden('#skF_2'(A_334,B_335,C_336),B_335)
      | r1_tarski(B_335,C_336)
      | ~ m1_subset_1(C_336,k1_zfmisc_1(A_334))
      | ~ m1_subset_1(B_335,k1_zfmisc_1(A_334)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3469,plain,(
    ! [B_355,C_356,A_357] :
      ( ~ v1_xboole_0(B_355)
      | r1_tarski(B_355,C_356)
      | ~ m1_subset_1(C_356,k1_zfmisc_1(A_357))
      | ~ m1_subset_1(B_355,k1_zfmisc_1(A_357)) ) ),
    inference(resolution,[status(thm)],[c_3294,c_12])).

tff(c_3546,plain,(
    ! [B_361] :
      ( ~ v1_xboole_0(B_361)
      | r1_tarski(B_361,'#skF_4')
      | ~ m1_subset_1(B_361,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_34,c_3469])).

tff(c_3561,plain,
    ( ~ v1_xboole_0('#skF_5')
    | r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_3546])).

tff(c_3572,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3135,c_3561])).

tff(c_3137,plain,(
    ! [D_312] :
      ( ~ r2_hidden(D_312,'#skF_4')
      | ~ m1_subset_1(D_312,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_3146,plain,(
    ! [B_9] :
      ( ~ m1_subset_1(B_9,'#skF_3')
      | ~ m1_subset_1(B_9,'#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_3137])).

tff(c_3149,plain,(
    ! [B_313] :
      ( ~ m1_subset_1(B_313,'#skF_3')
      | ~ m1_subset_1(B_313,'#skF_4') ) ),
    inference(splitLeft,[status(thm)],[c_3146])).

tff(c_3154,plain,(
    ! [B_9] :
      ( ~ m1_subset_1(B_9,'#skF_4')
      | ~ v1_xboole_0(B_9)
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_18,c_3149])).

tff(c_3155,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3154])).

tff(c_3168,plain,(
    ! [A_318,B_319] :
      ( m1_subset_1('#skF_1'(A_318,B_319),B_319)
      | v1_xboole_0(B_319)
      | ~ r2_xboole_0(A_318,B_319) ) ),
    inference(resolution,[status(thm)],[c_67,c_14])).

tff(c_3148,plain,(
    ! [B_9] :
      ( ~ m1_subset_1(B_9,'#skF_3')
      | ~ m1_subset_1(B_9,'#skF_4') ) ),
    inference(splitLeft,[status(thm)],[c_3146])).

tff(c_3172,plain,(
    ! [A_318] :
      ( ~ m1_subset_1('#skF_1'(A_318,'#skF_3'),'#skF_4')
      | v1_xboole_0('#skF_3')
      | ~ r2_xboole_0(A_318,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3168,c_3148])).

tff(c_3180,plain,(
    ! [A_320] :
      ( ~ m1_subset_1('#skF_1'(A_320,'#skF_3'),'#skF_4')
      | ~ r2_xboole_0(A_320,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_3155,c_3172])).

tff(c_3184,plain,(
    ! [A_320] :
      ( ~ r2_xboole_0(A_320,'#skF_3')
      | ~ v1_xboole_0('#skF_1'(A_320,'#skF_3'))
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_3180])).

tff(c_3186,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3184])).

tff(c_3156,plain,(
    ! [C_314,A_315,B_316] :
      ( r2_hidden(C_314,A_315)
      | ~ r2_hidden(C_314,B_316)
      | ~ m1_subset_1(B_316,k1_zfmisc_1(A_315)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3198,plain,(
    ! [B_323,A_324,A_325] :
      ( r2_hidden(B_323,A_324)
      | ~ m1_subset_1(A_325,k1_zfmisc_1(A_324))
      | ~ m1_subset_1(B_323,A_325)
      | v1_xboole_0(A_325) ) ),
    inference(resolution,[status(thm)],[c_16,c_3156])).

tff(c_3208,plain,(
    ! [B_323] :
      ( r2_hidden(B_323,'#skF_3')
      | ~ m1_subset_1(B_323,'#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_3198])).

tff(c_3216,plain,(
    ! [B_326] :
      ( r2_hidden(B_326,'#skF_3')
      | ~ m1_subset_1(B_326,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_3186,c_3208])).

tff(c_3225,plain,(
    ! [B_326] :
      ( m1_subset_1(B_326,'#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(B_326,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3216,c_14])).

tff(c_3249,plain,(
    ! [B_330] :
      ( m1_subset_1(B_330,'#skF_3')
      | ~ m1_subset_1(B_330,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_3155,c_3225])).

tff(c_3269,plain,(
    ! [B_331] : ~ m1_subset_1(B_331,'#skF_4') ),
    inference(resolution,[status(thm)],[c_3249,c_3148])).

tff(c_3277,plain,(
    ! [A_38] :
      ( v1_xboole_0('#skF_4')
      | ~ r2_xboole_0(A_38,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_74,c_3269])).

tff(c_3287,plain,(
    ! [A_332] : ~ r2_xboole_0(A_332,'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_3186,c_3277])).

tff(c_3292,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ r1_tarski(A_1,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2,c_3287])).

tff(c_3577,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3572,c_3292])).

tff(c_3584,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_3577])).

tff(c_3586,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_3184])).

tff(c_3710,plain,(
    ! [A_379,B_380,C_381] :
      ( r2_hidden('#skF_2'(A_379,B_380,C_381),B_380)
      | r1_tarski(B_380,C_381)
      | ~ m1_subset_1(C_381,k1_zfmisc_1(A_379))
      | ~ m1_subset_1(B_380,k1_zfmisc_1(A_379)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3778,plain,(
    ! [B_386,C_387,A_388] :
      ( ~ v1_xboole_0(B_386)
      | r1_tarski(B_386,C_387)
      | ~ m1_subset_1(C_387,k1_zfmisc_1(A_388))
      | ~ m1_subset_1(B_386,k1_zfmisc_1(A_388)) ) ),
    inference(resolution,[status(thm)],[c_3710,c_12])).

tff(c_3841,plain,(
    ! [B_394] :
      ( ~ v1_xboole_0(B_394)
      | r1_tarski(B_394,'#skF_4')
      | ~ m1_subset_1(B_394,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_34,c_3778])).

tff(c_3856,plain,
    ( ~ v1_xboole_0('#skF_5')
    | r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_3841])).

tff(c_3867,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3135,c_3856])).

tff(c_77,plain,(
    ! [A_42,B_43] :
      ( r2_xboole_0(A_42,B_43)
      | B_43 = A_42
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_75,plain,(
    ! [B_39,A_38] :
      ( ~ v1_xboole_0(B_39)
      | ~ r2_xboole_0(A_38,B_39) ) ),
    inference(resolution,[status(thm)],[c_67,c_12])).

tff(c_88,plain,(
    ! [B_43,A_42] :
      ( ~ v1_xboole_0(B_43)
      | B_43 = A_42
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(resolution,[status(thm)],[c_77,c_75])).

tff(c_3873,plain,
    ( ~ v1_xboole_0('#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3867,c_88])).

tff(c_3876,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3586,c_3873])).

tff(c_3878,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_3876])).

tff(c_3881,plain,(
    ! [B_395] :
      ( ~ m1_subset_1(B_395,'#skF_4')
      | ~ v1_xboole_0(B_395) ) ),
    inference(splitRight,[status(thm)],[c_3154])).

tff(c_3886,plain,(
    ! [B_9] :
      ( ~ v1_xboole_0(B_9)
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_3881])).

tff(c_3887,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3886])).

tff(c_3880,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_3154])).

tff(c_3888,plain,(
    ! [C_396,A_397,B_398] :
      ( r2_hidden(C_396,A_397)
      | ~ r2_hidden(C_396,B_398)
      | ~ m1_subset_1(B_398,k1_zfmisc_1(A_397)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3932,plain,(
    ! [B_405,A_406,A_407] :
      ( r2_hidden(B_405,A_406)
      | ~ m1_subset_1(A_407,k1_zfmisc_1(A_406))
      | ~ m1_subset_1(B_405,A_407)
      | v1_xboole_0(A_407) ) ),
    inference(resolution,[status(thm)],[c_16,c_3888])).

tff(c_3942,plain,(
    ! [B_405] :
      ( r2_hidden(B_405,'#skF_3')
      | ~ m1_subset_1(B_405,'#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_3932])).

tff(c_3950,plain,(
    ! [B_408] :
      ( r2_hidden(B_408,'#skF_3')
      | ~ m1_subset_1(B_408,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_3887,c_3942])).

tff(c_3962,plain,(
    ! [B_408] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ m1_subset_1(B_408,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3950,c_12])).

tff(c_3970,plain,(
    ! [B_409] : ~ m1_subset_1(B_409,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3880,c_3962])).

tff(c_3974,plain,(
    ! [A_38] :
      ( v1_xboole_0('#skF_4')
      | ~ r2_xboole_0(A_38,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_74,c_3970])).

tff(c_3983,plain,(
    ! [A_410] : ~ r2_xboole_0(A_410,'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_3887,c_3974])).

tff(c_3988,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ r1_tarski(A_1,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2,c_3983])).

tff(c_4336,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4331,c_3988])).

tff(c_4343,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_4336])).

tff(c_4344,plain,(
    ! [B_9] : ~ v1_xboole_0(B_9) ),
    inference(splitRight,[status(thm)],[c_3886])).

tff(c_4352,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4344,c_3880])).

tff(c_4353,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_3146])).

tff(c_4583,plain,(
    ! [A_484,B_485,C_486] :
      ( r2_hidden('#skF_2'(A_484,B_485,C_486),B_485)
      | r1_tarski(B_485,C_486)
      | ~ m1_subset_1(C_486,k1_zfmisc_1(A_484))
      | ~ m1_subset_1(B_485,k1_zfmisc_1(A_484)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4669,plain,(
    ! [B_492,C_493,A_494] :
      ( ~ v1_xboole_0(B_492)
      | r1_tarski(B_492,C_493)
      | ~ m1_subset_1(C_493,k1_zfmisc_1(A_494))
      | ~ m1_subset_1(B_492,k1_zfmisc_1(A_494)) ) ),
    inference(resolution,[status(thm)],[c_4583,c_12])).

tff(c_4690,plain,(
    ! [B_495] :
      ( ~ v1_xboole_0(B_495)
      | r1_tarski(B_495,'#skF_5')
      | ~ m1_subset_1(B_495,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_32,c_4669])).

tff(c_4708,plain,
    ( ~ v1_xboole_0('#skF_4')
    | r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_4690])).

tff(c_4719,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4353,c_4708])).

tff(c_4722,plain,
    ( ~ v1_xboole_0('#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4719,c_88])).

tff(c_4725,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3135,c_4722])).

tff(c_4727,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_4725])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:10:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.48/2.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.48/2.12  
% 5.48/2.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.62/2.12  %$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 5.62/2.12  
% 5.62/2.12  %Foreground sorts:
% 5.62/2.12  
% 5.62/2.12  
% 5.62/2.12  %Background operators:
% 5.62/2.12  
% 5.62/2.12  
% 5.62/2.12  %Foreground operators:
% 5.62/2.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.62/2.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.62/2.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.62/2.12  tff('#skF_5', type, '#skF_5': $i).
% 5.62/2.12  tff('#skF_3', type, '#skF_3': $i).
% 5.62/2.12  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.62/2.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.62/2.12  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 5.62/2.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.62/2.12  tff('#skF_4', type, '#skF_4': $i).
% 5.62/2.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.62/2.12  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.62/2.12  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.62/2.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.62/2.12  
% 5.67/2.15  tff(f_96, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_subset_1)).
% 5.67/2.15  tff(f_47, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 5.67/2.15  tff(f_60, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 5.67/2.15  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 5.67/2.15  tff(f_42, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 5.67/2.15  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 5.67/2.15  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 5.67/2.15  tff(c_30, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.67/2.15  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.67/2.15  tff(c_57, plain, (![D_35]: (r2_hidden(D_35, '#skF_5') | ~r2_hidden(D_35, '#skF_4') | ~m1_subset_1(D_35, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.67/2.15  tff(c_12, plain, (![B_7, A_6]: (~v1_xboole_0(B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.67/2.15  tff(c_61, plain, (![D_35]: (~v1_xboole_0('#skF_5') | ~r2_hidden(D_35, '#skF_4') | ~m1_subset_1(D_35, '#skF_3'))), inference(resolution, [status(thm)], [c_57, c_12])).
% 5.67/2.15  tff(c_133, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_61])).
% 5.67/2.15  tff(c_16, plain, (![B_9, A_8]: (r2_hidden(B_9, A_8) | ~m1_subset_1(B_9, A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.67/2.15  tff(c_118, plain, (![D_50]: (r2_hidden(D_50, '#skF_4') | ~r2_hidden(D_50, '#skF_5') | ~m1_subset_1(D_50, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.67/2.15  tff(c_130, plain, (![B_9]: (r2_hidden(B_9, '#skF_4') | ~m1_subset_1(B_9, '#skF_3') | ~m1_subset_1(B_9, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_16, c_118])).
% 5.67/2.15  tff(c_178, plain, (![B_61]: (r2_hidden(B_61, '#skF_4') | ~m1_subset_1(B_61, '#skF_3') | ~m1_subset_1(B_61, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_133, c_130])).
% 5.67/2.15  tff(c_194, plain, (![B_61]: (~v1_xboole_0('#skF_4') | ~m1_subset_1(B_61, '#skF_3') | ~m1_subset_1(B_61, '#skF_5'))), inference(resolution, [status(thm)], [c_178, c_12])).
% 5.67/2.15  tff(c_195, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_194])).
% 5.67/2.15  tff(c_2, plain, (![A_1, B_2]: (r2_xboole_0(A_1, B_2) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.67/2.15  tff(c_10, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | ~r2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.67/2.15  tff(c_38, plain, (![D_25]: (r2_hidden(D_25, '#skF_5') | ~r2_hidden(D_25, '#skF_4') | ~m1_subset_1(D_25, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.67/2.15  tff(c_102, plain, (![A_48, B_49]: (~r2_hidden('#skF_1'(A_48, B_49), A_48) | ~r2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.67/2.15  tff(c_509, plain, (![B_87]: (~r2_xboole_0('#skF_5', B_87) | ~r2_hidden('#skF_1'('#skF_5', B_87), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_5', B_87), '#skF_3'))), inference(resolution, [status(thm)], [c_38, c_102])).
% 5.67/2.15  tff(c_534, plain, (~m1_subset_1('#skF_1'('#skF_5', '#skF_4'), '#skF_3') | ~r2_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_10, c_509])).
% 5.67/2.15  tff(c_561, plain, (~r2_xboole_0('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_534])).
% 5.67/2.15  tff(c_564, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_2, c_561])).
% 5.67/2.15  tff(c_567, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_30, c_564])).
% 5.67/2.15  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.67/2.15  tff(c_28, plain, (![A_14, B_15, C_19]: (m1_subset_1('#skF_2'(A_14, B_15, C_19), A_14) | r1_tarski(B_15, C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.67/2.15  tff(c_160, plain, (![A_58, B_59, C_60]: (r2_hidden('#skF_2'(A_58, B_59, C_60), B_59) | r1_tarski(B_59, C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(A_58)) | ~m1_subset_1(B_59, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.67/2.15  tff(c_36, plain, (![D_25]: (r2_hidden(D_25, '#skF_4') | ~r2_hidden(D_25, '#skF_5') | ~m1_subset_1(D_25, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.67/2.15  tff(c_1025, plain, (![A_132, C_133]: (r2_hidden('#skF_2'(A_132, '#skF_5', C_133), '#skF_4') | ~m1_subset_1('#skF_2'(A_132, '#skF_5', C_133), '#skF_3') | r1_tarski('#skF_5', C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(A_132)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_132)))), inference(resolution, [status(thm)], [c_160, c_36])).
% 5.67/2.15  tff(c_24, plain, (![A_14, B_15, C_19]: (~r2_hidden('#skF_2'(A_14, B_15, C_19), C_19) | r1_tarski(B_15, C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.67/2.15  tff(c_1029, plain, (![A_132]: (~m1_subset_1('#skF_2'(A_132, '#skF_5', '#skF_4'), '#skF_3') | r1_tarski('#skF_5', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_132)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_132)))), inference(resolution, [status(thm)], [c_1025, c_24])).
% 5.67/2.15  tff(c_1694, plain, (![A_168]: (~m1_subset_1('#skF_2'(A_168, '#skF_5', '#skF_4'), '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_168)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_168)))), inference(negUnitSimplification, [status(thm)], [c_567, c_567, c_1029])).
% 5.67/2.15  tff(c_1701, plain, (r1_tarski('#skF_5', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_1694])).
% 5.67/2.15  tff(c_1708, plain, (r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_1701])).
% 5.67/2.15  tff(c_1710, plain, $false, inference(negUnitSimplification, [status(thm)], [c_567, c_1708])).
% 5.67/2.15  tff(c_1712, plain, (r2_xboole_0('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_534])).
% 5.67/2.15  tff(c_67, plain, (![A_38, B_39]: (r2_hidden('#skF_1'(A_38, B_39), B_39) | ~r2_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.67/2.15  tff(c_14, plain, (![B_9, A_8]: (m1_subset_1(B_9, A_8) | ~r2_hidden(B_9, A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.67/2.15  tff(c_74, plain, (![A_38, B_39]: (m1_subset_1('#skF_1'(A_38, B_39), B_39) | v1_xboole_0(B_39) | ~r2_xboole_0(A_38, B_39))), inference(resolution, [status(thm)], [c_67, c_14])).
% 5.67/2.15  tff(c_134, plain, (![C_51, A_52, B_53]: (r2_hidden(C_51, A_52) | ~r2_hidden(C_51, B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.67/2.15  tff(c_249, plain, (![B_65, A_66, A_67]: (r2_hidden(B_65, A_66) | ~m1_subset_1(A_67, k1_zfmisc_1(A_66)) | ~m1_subset_1(B_65, A_67) | v1_xboole_0(A_67))), inference(resolution, [status(thm)], [c_16, c_134])).
% 5.67/2.15  tff(c_257, plain, (![B_65]: (r2_hidden(B_65, '#skF_3') | ~m1_subset_1(B_65, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_32, c_249])).
% 5.67/2.15  tff(c_268, plain, (![B_68]: (r2_hidden(B_68, '#skF_3') | ~m1_subset_1(B_68, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_133, c_257])).
% 5.67/2.15  tff(c_284, plain, (![B_68]: (~v1_xboole_0('#skF_3') | ~m1_subset_1(B_68, '#skF_5'))), inference(resolution, [status(thm)], [c_268, c_12])).
% 5.67/2.15  tff(c_285, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_284])).
% 5.67/2.15  tff(c_259, plain, (![B_65]: (r2_hidden(B_65, '#skF_3') | ~m1_subset_1(B_65, '#skF_4') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_249])).
% 5.67/2.15  tff(c_300, plain, (![B_72]: (r2_hidden(B_72, '#skF_3') | ~m1_subset_1(B_72, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_195, c_259])).
% 5.67/2.15  tff(c_309, plain, (![B_72]: (m1_subset_1(B_72, '#skF_3') | v1_xboole_0('#skF_3') | ~m1_subset_1(B_72, '#skF_4'))), inference(resolution, [status(thm)], [c_300, c_14])).
% 5.67/2.15  tff(c_317, plain, (![B_72]: (m1_subset_1(B_72, '#skF_3') | ~m1_subset_1(B_72, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_285, c_309])).
% 5.67/2.15  tff(c_1711, plain, (~m1_subset_1('#skF_1'('#skF_5', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_534])).
% 5.67/2.15  tff(c_1732, plain, (~m1_subset_1('#skF_1'('#skF_5', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_317, c_1711])).
% 5.67/2.15  tff(c_1744, plain, (v1_xboole_0('#skF_4') | ~r2_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_74, c_1732])).
% 5.67/2.15  tff(c_1750, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1712, c_1744])).
% 5.67/2.15  tff(c_1752, plain, $false, inference(negUnitSimplification, [status(thm)], [c_195, c_1750])).
% 5.67/2.15  tff(c_1754, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_284])).
% 5.67/2.15  tff(c_1777, plain, (![A_174, B_175, C_176]: (m1_subset_1('#skF_2'(A_174, B_175, C_176), A_174) | r1_tarski(B_175, C_176) | ~m1_subset_1(C_176, k1_zfmisc_1(A_174)) | ~m1_subset_1(B_175, k1_zfmisc_1(A_174)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.67/2.15  tff(c_20, plain, (![B_9, A_8]: (v1_xboole_0(B_9) | ~m1_subset_1(B_9, A_8) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.67/2.15  tff(c_2210, plain, (![A_222, B_223, C_224]: (v1_xboole_0('#skF_2'(A_222, B_223, C_224)) | ~v1_xboole_0(A_222) | r1_tarski(B_223, C_224) | ~m1_subset_1(C_224, k1_zfmisc_1(A_222)) | ~m1_subset_1(B_223, k1_zfmisc_1(A_222)))), inference(resolution, [status(thm)], [c_1777, c_20])).
% 5.67/2.15  tff(c_2223, plain, (![B_223]: (v1_xboole_0('#skF_2'('#skF_3', B_223, '#skF_4')) | ~v1_xboole_0('#skF_3') | r1_tarski(B_223, '#skF_4') | ~m1_subset_1(B_223, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_34, c_2210])).
% 5.67/2.15  tff(c_2298, plain, (![B_228]: (v1_xboole_0('#skF_2'('#skF_3', B_228, '#skF_4')) | r1_tarski(B_228, '#skF_4') | ~m1_subset_1(B_228, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1754, c_2223])).
% 5.67/2.15  tff(c_2322, plain, (v1_xboole_0('#skF_2'('#skF_3', '#skF_5', '#skF_4')) | r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_2298])).
% 5.67/2.15  tff(c_2325, plain, (r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_2322])).
% 5.67/2.15  tff(c_1809, plain, (![B_178]: (r2_hidden(B_178, '#skF_3') | ~m1_subset_1(B_178, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_195, c_259])).
% 5.67/2.15  tff(c_1821, plain, (![B_178]: (~v1_xboole_0('#skF_3') | ~m1_subset_1(B_178, '#skF_4'))), inference(resolution, [status(thm)], [c_1809, c_12])).
% 5.67/2.15  tff(c_1829, plain, (![B_179]: (~m1_subset_1(B_179, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1754, c_1821])).
% 5.67/2.15  tff(c_1837, plain, (![A_38]: (v1_xboole_0('#skF_4') | ~r2_xboole_0(A_38, '#skF_4'))), inference(resolution, [status(thm)], [c_74, c_1829])).
% 5.67/2.15  tff(c_1847, plain, (![A_180]: (~r2_xboole_0(A_180, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_195, c_1837])).
% 5.67/2.15  tff(c_1852, plain, (![A_1]: (A_1='#skF_4' | ~r1_tarski(A_1, '#skF_4'))), inference(resolution, [status(thm)], [c_2, c_1847])).
% 5.67/2.15  tff(c_2328, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_2325, c_1852])).
% 5.67/2.15  tff(c_2335, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_2328])).
% 5.67/2.15  tff(c_2337, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_2322])).
% 5.67/2.15  tff(c_2275, plain, (![A_226, C_227]: (r2_hidden('#skF_2'(A_226, '#skF_5', C_227), '#skF_4') | ~m1_subset_1('#skF_2'(A_226, '#skF_5', C_227), '#skF_3') | r1_tarski('#skF_5', C_227) | ~m1_subset_1(C_227, k1_zfmisc_1(A_226)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_226)))), inference(resolution, [status(thm)], [c_160, c_36])).
% 5.67/2.15  tff(c_2291, plain, (![A_226]: (~m1_subset_1('#skF_2'(A_226, '#skF_5', '#skF_4'), '#skF_3') | r1_tarski('#skF_5', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_226)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_226)))), inference(resolution, [status(thm)], [c_2275, c_24])).
% 5.67/2.15  tff(c_2350, plain, (![A_232]: (~m1_subset_1('#skF_2'(A_232, '#skF_5', '#skF_4'), '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_232)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_232)))), inference(negUnitSimplification, [status(thm)], [c_2337, c_2291])).
% 5.67/2.15  tff(c_2354, plain, (r1_tarski('#skF_5', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_2350])).
% 5.67/2.15  tff(c_2360, plain, (r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_2354])).
% 5.67/2.15  tff(c_2362, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2337, c_2360])).
% 5.67/2.15  tff(c_2364, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_194])).
% 5.67/2.15  tff(c_3074, plain, (![B_308, C_309, A_310]: (~v1_xboole_0(B_308) | r1_tarski(B_308, C_309) | ~m1_subset_1(C_309, k1_zfmisc_1(A_310)) | ~m1_subset_1(B_308, k1_zfmisc_1(A_310)))), inference(resolution, [status(thm)], [c_160, c_12])).
% 5.67/2.15  tff(c_3095, plain, (![B_311]: (~v1_xboole_0(B_311) | r1_tarski(B_311, '#skF_5') | ~m1_subset_1(B_311, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_32, c_3074])).
% 5.67/2.15  tff(c_3113, plain, (~v1_xboole_0('#skF_4') | r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_34, c_3095])).
% 5.67/2.15  tff(c_3123, plain, (r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2364, c_3113])).
% 5.67/2.15  tff(c_2673, plain, (![B_263, C_264, A_265]: (~v1_xboole_0(B_263) | r1_tarski(B_263, C_264) | ~m1_subset_1(C_264, k1_zfmisc_1(A_265)) | ~m1_subset_1(B_263, k1_zfmisc_1(A_265)))), inference(resolution, [status(thm)], [c_160, c_12])).
% 5.67/2.15  tff(c_2694, plain, (![B_266]: (~v1_xboole_0(B_266) | r1_tarski(B_266, '#skF_5') | ~m1_subset_1(B_266, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_32, c_2673])).
% 5.67/2.15  tff(c_2712, plain, (~v1_xboole_0('#skF_4') | r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_34, c_2694])).
% 5.67/2.15  tff(c_2722, plain, (r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2364, c_2712])).
% 5.67/2.15  tff(c_18, plain, (![B_9, A_8]: (m1_subset_1(B_9, A_8) | ~v1_xboole_0(B_9) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.67/2.15  tff(c_2365, plain, (![B_233]: (~m1_subset_1(B_233, '#skF_3') | ~m1_subset_1(B_233, '#skF_5'))), inference(splitRight, [status(thm)], [c_194])).
% 5.67/2.15  tff(c_2369, plain, (![A_38]: (~m1_subset_1('#skF_1'(A_38, '#skF_5'), '#skF_3') | v1_xboole_0('#skF_5') | ~r2_xboole_0(A_38, '#skF_5'))), inference(resolution, [status(thm)], [c_74, c_2365])).
% 5.67/2.15  tff(c_2378, plain, (![A_234]: (~m1_subset_1('#skF_1'(A_234, '#skF_5'), '#skF_3') | ~r2_xboole_0(A_234, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_133, c_2369])).
% 5.67/2.15  tff(c_2382, plain, (![A_234]: (~r2_xboole_0(A_234, '#skF_5') | ~v1_xboole_0('#skF_1'(A_234, '#skF_5')) | ~v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_18, c_2378])).
% 5.67/2.15  tff(c_2383, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_2382])).
% 5.67/2.15  tff(c_2447, plain, (![B_242, A_243, A_244]: (r2_hidden(B_242, A_243) | ~m1_subset_1(A_244, k1_zfmisc_1(A_243)) | ~m1_subset_1(B_242, A_244) | v1_xboole_0(A_244))), inference(resolution, [status(thm)], [c_16, c_134])).
% 5.67/2.15  tff(c_2455, plain, (![B_242]: (r2_hidden(B_242, '#skF_3') | ~m1_subset_1(B_242, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_32, c_2447])).
% 5.67/2.15  tff(c_2467, plain, (![B_245]: (r2_hidden(B_245, '#skF_3') | ~m1_subset_1(B_245, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_133, c_2455])).
% 5.67/2.15  tff(c_2480, plain, (![B_245]: (m1_subset_1(B_245, '#skF_3') | v1_xboole_0('#skF_3') | ~m1_subset_1(B_245, '#skF_5'))), inference(resolution, [status(thm)], [c_2467, c_14])).
% 5.67/2.15  tff(c_2509, plain, (![B_249]: (m1_subset_1(B_249, '#skF_3') | ~m1_subset_1(B_249, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_2383, c_2480])).
% 5.67/2.15  tff(c_2517, plain, (![A_38]: (m1_subset_1('#skF_1'(A_38, '#skF_5'), '#skF_3') | v1_xboole_0('#skF_5') | ~r2_xboole_0(A_38, '#skF_5'))), inference(resolution, [status(thm)], [c_74, c_2509])).
% 5.67/2.15  tff(c_2625, plain, (![A_257]: (m1_subset_1('#skF_1'(A_257, '#skF_5'), '#skF_3') | ~r2_xboole_0(A_257, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_133, c_2517])).
% 5.67/2.15  tff(c_2376, plain, (![A_38]: (~m1_subset_1('#skF_1'(A_38, '#skF_5'), '#skF_3') | ~r2_xboole_0(A_38, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_133, c_2369])).
% 5.67/2.15  tff(c_2640, plain, (![A_258]: (~r2_xboole_0(A_258, '#skF_5'))), inference(resolution, [status(thm)], [c_2625, c_2376])).
% 5.67/2.15  tff(c_2645, plain, (![A_1]: (A_1='#skF_5' | ~r1_tarski(A_1, '#skF_5'))), inference(resolution, [status(thm)], [c_2, c_2640])).
% 5.67/2.15  tff(c_2725, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_2722, c_2645])).
% 5.67/2.15  tff(c_2732, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_2725])).
% 5.67/2.15  tff(c_2734, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_2382])).
% 5.67/2.15  tff(c_2755, plain, (![B_269, A_270, A_271]: (r2_hidden(B_269, A_270) | ~m1_subset_1(A_271, k1_zfmisc_1(A_270)) | ~m1_subset_1(B_269, A_271) | v1_xboole_0(A_271))), inference(resolution, [status(thm)], [c_16, c_134])).
% 5.67/2.15  tff(c_2763, plain, (![B_269]: (r2_hidden(B_269, '#skF_3') | ~m1_subset_1(B_269, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_32, c_2755])).
% 5.67/2.15  tff(c_2773, plain, (![B_272]: (r2_hidden(B_272, '#skF_3') | ~m1_subset_1(B_272, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_133, c_2763])).
% 5.67/2.15  tff(c_2785, plain, (![B_272]: (~v1_xboole_0('#skF_3') | ~m1_subset_1(B_272, '#skF_5'))), inference(resolution, [status(thm)], [c_2773, c_12])).
% 5.67/2.15  tff(c_2794, plain, (![B_273]: (~m1_subset_1(B_273, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2734, c_2785])).
% 5.67/2.15  tff(c_2798, plain, (![A_38]: (v1_xboole_0('#skF_5') | ~r2_xboole_0(A_38, '#skF_5'))), inference(resolution, [status(thm)], [c_74, c_2794])).
% 5.67/2.15  tff(c_2823, plain, (![A_277]: (~r2_xboole_0(A_277, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_133, c_2798])).
% 5.67/2.15  tff(c_2828, plain, (![A_1]: (A_1='#skF_5' | ~r1_tarski(A_1, '#skF_5'))), inference(resolution, [status(thm)], [c_2, c_2823])).
% 5.67/2.15  tff(c_3126, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_3123, c_2828])).
% 5.67/2.15  tff(c_3133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_3126])).
% 5.67/2.15  tff(c_3135, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_61])).
% 5.67/2.15  tff(c_4073, plain, (![A_422, B_423, C_424]: (r2_hidden('#skF_2'(A_422, B_423, C_424), B_423) | r1_tarski(B_423, C_424) | ~m1_subset_1(C_424, k1_zfmisc_1(A_422)) | ~m1_subset_1(B_423, k1_zfmisc_1(A_422)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.67/2.15  tff(c_4256, plain, (![B_446, C_447, A_448]: (~v1_xboole_0(B_446) | r1_tarski(B_446, C_447) | ~m1_subset_1(C_447, k1_zfmisc_1(A_448)) | ~m1_subset_1(B_446, k1_zfmisc_1(A_448)))), inference(resolution, [status(thm)], [c_4073, c_12])).
% 5.67/2.15  tff(c_4305, plain, (![B_450]: (~v1_xboole_0(B_450) | r1_tarski(B_450, '#skF_4') | ~m1_subset_1(B_450, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_34, c_4256])).
% 5.67/2.15  tff(c_4320, plain, (~v1_xboole_0('#skF_5') | r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_4305])).
% 5.67/2.15  tff(c_4331, plain, (r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3135, c_4320])).
% 5.67/2.15  tff(c_3294, plain, (![A_334, B_335, C_336]: (r2_hidden('#skF_2'(A_334, B_335, C_336), B_335) | r1_tarski(B_335, C_336) | ~m1_subset_1(C_336, k1_zfmisc_1(A_334)) | ~m1_subset_1(B_335, k1_zfmisc_1(A_334)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.67/2.15  tff(c_3469, plain, (![B_355, C_356, A_357]: (~v1_xboole_0(B_355) | r1_tarski(B_355, C_356) | ~m1_subset_1(C_356, k1_zfmisc_1(A_357)) | ~m1_subset_1(B_355, k1_zfmisc_1(A_357)))), inference(resolution, [status(thm)], [c_3294, c_12])).
% 5.67/2.15  tff(c_3546, plain, (![B_361]: (~v1_xboole_0(B_361) | r1_tarski(B_361, '#skF_4') | ~m1_subset_1(B_361, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_34, c_3469])).
% 5.67/2.15  tff(c_3561, plain, (~v1_xboole_0('#skF_5') | r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_3546])).
% 5.67/2.15  tff(c_3572, plain, (r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3135, c_3561])).
% 5.67/2.15  tff(c_3137, plain, (![D_312]: (~r2_hidden(D_312, '#skF_4') | ~m1_subset_1(D_312, '#skF_3'))), inference(splitRight, [status(thm)], [c_61])).
% 5.67/2.15  tff(c_3146, plain, (![B_9]: (~m1_subset_1(B_9, '#skF_3') | ~m1_subset_1(B_9, '#skF_4') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_16, c_3137])).
% 5.67/2.15  tff(c_3149, plain, (![B_313]: (~m1_subset_1(B_313, '#skF_3') | ~m1_subset_1(B_313, '#skF_4'))), inference(splitLeft, [status(thm)], [c_3146])).
% 5.67/2.15  tff(c_3154, plain, (![B_9]: (~m1_subset_1(B_9, '#skF_4') | ~v1_xboole_0(B_9) | ~v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_18, c_3149])).
% 5.67/2.15  tff(c_3155, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_3154])).
% 5.67/2.15  tff(c_3168, plain, (![A_318, B_319]: (m1_subset_1('#skF_1'(A_318, B_319), B_319) | v1_xboole_0(B_319) | ~r2_xboole_0(A_318, B_319))), inference(resolution, [status(thm)], [c_67, c_14])).
% 5.67/2.15  tff(c_3148, plain, (![B_9]: (~m1_subset_1(B_9, '#skF_3') | ~m1_subset_1(B_9, '#skF_4'))), inference(splitLeft, [status(thm)], [c_3146])).
% 5.67/2.15  tff(c_3172, plain, (![A_318]: (~m1_subset_1('#skF_1'(A_318, '#skF_3'), '#skF_4') | v1_xboole_0('#skF_3') | ~r2_xboole_0(A_318, '#skF_3'))), inference(resolution, [status(thm)], [c_3168, c_3148])).
% 5.67/2.15  tff(c_3180, plain, (![A_320]: (~m1_subset_1('#skF_1'(A_320, '#skF_3'), '#skF_4') | ~r2_xboole_0(A_320, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_3155, c_3172])).
% 5.67/2.15  tff(c_3184, plain, (![A_320]: (~r2_xboole_0(A_320, '#skF_3') | ~v1_xboole_0('#skF_1'(A_320, '#skF_3')) | ~v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_3180])).
% 5.67/2.15  tff(c_3186, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_3184])).
% 5.67/2.15  tff(c_3156, plain, (![C_314, A_315, B_316]: (r2_hidden(C_314, A_315) | ~r2_hidden(C_314, B_316) | ~m1_subset_1(B_316, k1_zfmisc_1(A_315)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.67/2.15  tff(c_3198, plain, (![B_323, A_324, A_325]: (r2_hidden(B_323, A_324) | ~m1_subset_1(A_325, k1_zfmisc_1(A_324)) | ~m1_subset_1(B_323, A_325) | v1_xboole_0(A_325))), inference(resolution, [status(thm)], [c_16, c_3156])).
% 5.67/2.15  tff(c_3208, plain, (![B_323]: (r2_hidden(B_323, '#skF_3') | ~m1_subset_1(B_323, '#skF_4') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_3198])).
% 5.67/2.15  tff(c_3216, plain, (![B_326]: (r2_hidden(B_326, '#skF_3') | ~m1_subset_1(B_326, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_3186, c_3208])).
% 5.67/2.15  tff(c_3225, plain, (![B_326]: (m1_subset_1(B_326, '#skF_3') | v1_xboole_0('#skF_3') | ~m1_subset_1(B_326, '#skF_4'))), inference(resolution, [status(thm)], [c_3216, c_14])).
% 5.67/2.15  tff(c_3249, plain, (![B_330]: (m1_subset_1(B_330, '#skF_3') | ~m1_subset_1(B_330, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_3155, c_3225])).
% 5.67/2.15  tff(c_3269, plain, (![B_331]: (~m1_subset_1(B_331, '#skF_4'))), inference(resolution, [status(thm)], [c_3249, c_3148])).
% 5.67/2.15  tff(c_3277, plain, (![A_38]: (v1_xboole_0('#skF_4') | ~r2_xboole_0(A_38, '#skF_4'))), inference(resolution, [status(thm)], [c_74, c_3269])).
% 5.67/2.15  tff(c_3287, plain, (![A_332]: (~r2_xboole_0(A_332, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_3186, c_3277])).
% 5.67/2.15  tff(c_3292, plain, (![A_1]: (A_1='#skF_4' | ~r1_tarski(A_1, '#skF_4'))), inference(resolution, [status(thm)], [c_2, c_3287])).
% 5.67/2.15  tff(c_3577, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_3572, c_3292])).
% 5.67/2.15  tff(c_3584, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_3577])).
% 5.67/2.15  tff(c_3586, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_3184])).
% 5.67/2.15  tff(c_3710, plain, (![A_379, B_380, C_381]: (r2_hidden('#skF_2'(A_379, B_380, C_381), B_380) | r1_tarski(B_380, C_381) | ~m1_subset_1(C_381, k1_zfmisc_1(A_379)) | ~m1_subset_1(B_380, k1_zfmisc_1(A_379)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.67/2.15  tff(c_3778, plain, (![B_386, C_387, A_388]: (~v1_xboole_0(B_386) | r1_tarski(B_386, C_387) | ~m1_subset_1(C_387, k1_zfmisc_1(A_388)) | ~m1_subset_1(B_386, k1_zfmisc_1(A_388)))), inference(resolution, [status(thm)], [c_3710, c_12])).
% 5.67/2.15  tff(c_3841, plain, (![B_394]: (~v1_xboole_0(B_394) | r1_tarski(B_394, '#skF_4') | ~m1_subset_1(B_394, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_34, c_3778])).
% 5.67/2.15  tff(c_3856, plain, (~v1_xboole_0('#skF_5') | r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_3841])).
% 5.67/2.15  tff(c_3867, plain, (r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3135, c_3856])).
% 5.67/2.15  tff(c_77, plain, (![A_42, B_43]: (r2_xboole_0(A_42, B_43) | B_43=A_42 | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.67/2.15  tff(c_75, plain, (![B_39, A_38]: (~v1_xboole_0(B_39) | ~r2_xboole_0(A_38, B_39))), inference(resolution, [status(thm)], [c_67, c_12])).
% 5.67/2.15  tff(c_88, plain, (![B_43, A_42]: (~v1_xboole_0(B_43) | B_43=A_42 | ~r1_tarski(A_42, B_43))), inference(resolution, [status(thm)], [c_77, c_75])).
% 5.67/2.15  tff(c_3873, plain, (~v1_xboole_0('#skF_4') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_3867, c_88])).
% 5.67/2.15  tff(c_3876, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3586, c_3873])).
% 5.67/2.15  tff(c_3878, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_3876])).
% 5.67/2.15  tff(c_3881, plain, (![B_395]: (~m1_subset_1(B_395, '#skF_4') | ~v1_xboole_0(B_395))), inference(splitRight, [status(thm)], [c_3154])).
% 5.67/2.15  tff(c_3886, plain, (![B_9]: (~v1_xboole_0(B_9) | ~v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_3881])).
% 5.67/2.15  tff(c_3887, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_3886])).
% 5.67/2.15  tff(c_3880, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_3154])).
% 5.67/2.15  tff(c_3888, plain, (![C_396, A_397, B_398]: (r2_hidden(C_396, A_397) | ~r2_hidden(C_396, B_398) | ~m1_subset_1(B_398, k1_zfmisc_1(A_397)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.67/2.15  tff(c_3932, plain, (![B_405, A_406, A_407]: (r2_hidden(B_405, A_406) | ~m1_subset_1(A_407, k1_zfmisc_1(A_406)) | ~m1_subset_1(B_405, A_407) | v1_xboole_0(A_407))), inference(resolution, [status(thm)], [c_16, c_3888])).
% 5.67/2.15  tff(c_3942, plain, (![B_405]: (r2_hidden(B_405, '#skF_3') | ~m1_subset_1(B_405, '#skF_4') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_3932])).
% 5.67/2.15  tff(c_3950, plain, (![B_408]: (r2_hidden(B_408, '#skF_3') | ~m1_subset_1(B_408, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_3887, c_3942])).
% 5.67/2.15  tff(c_3962, plain, (![B_408]: (~v1_xboole_0('#skF_3') | ~m1_subset_1(B_408, '#skF_4'))), inference(resolution, [status(thm)], [c_3950, c_12])).
% 5.67/2.15  tff(c_3970, plain, (![B_409]: (~m1_subset_1(B_409, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3880, c_3962])).
% 5.67/2.15  tff(c_3974, plain, (![A_38]: (v1_xboole_0('#skF_4') | ~r2_xboole_0(A_38, '#skF_4'))), inference(resolution, [status(thm)], [c_74, c_3970])).
% 5.67/2.15  tff(c_3983, plain, (![A_410]: (~r2_xboole_0(A_410, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_3887, c_3974])).
% 5.67/2.15  tff(c_3988, plain, (![A_1]: (A_1='#skF_4' | ~r1_tarski(A_1, '#skF_4'))), inference(resolution, [status(thm)], [c_2, c_3983])).
% 5.67/2.15  tff(c_4336, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_4331, c_3988])).
% 5.67/2.15  tff(c_4343, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_4336])).
% 5.67/2.15  tff(c_4344, plain, (![B_9]: (~v1_xboole_0(B_9))), inference(splitRight, [status(thm)], [c_3886])).
% 5.67/2.15  tff(c_4352, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4344, c_3880])).
% 5.67/2.15  tff(c_4353, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_3146])).
% 5.67/2.15  tff(c_4583, plain, (![A_484, B_485, C_486]: (r2_hidden('#skF_2'(A_484, B_485, C_486), B_485) | r1_tarski(B_485, C_486) | ~m1_subset_1(C_486, k1_zfmisc_1(A_484)) | ~m1_subset_1(B_485, k1_zfmisc_1(A_484)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.67/2.15  tff(c_4669, plain, (![B_492, C_493, A_494]: (~v1_xboole_0(B_492) | r1_tarski(B_492, C_493) | ~m1_subset_1(C_493, k1_zfmisc_1(A_494)) | ~m1_subset_1(B_492, k1_zfmisc_1(A_494)))), inference(resolution, [status(thm)], [c_4583, c_12])).
% 5.67/2.15  tff(c_4690, plain, (![B_495]: (~v1_xboole_0(B_495) | r1_tarski(B_495, '#skF_5') | ~m1_subset_1(B_495, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_32, c_4669])).
% 5.67/2.15  tff(c_4708, plain, (~v1_xboole_0('#skF_4') | r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_34, c_4690])).
% 5.67/2.15  tff(c_4719, plain, (r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4353, c_4708])).
% 5.67/2.15  tff(c_4722, plain, (~v1_xboole_0('#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_4719, c_88])).
% 5.67/2.15  tff(c_4725, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3135, c_4722])).
% 5.67/2.15  tff(c_4727, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_4725])).
% 5.67/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.67/2.15  
% 5.67/2.15  Inference rules
% 5.67/2.15  ----------------------
% 5.67/2.15  #Ref     : 0
% 5.67/2.15  #Sup     : 912
% 5.67/2.15  #Fact    : 0
% 5.67/2.15  #Define  : 0
% 5.67/2.15  #Split   : 42
% 5.67/2.15  #Chain   : 0
% 5.67/2.15  #Close   : 0
% 5.67/2.15  
% 5.67/2.15  Ordering : KBO
% 5.67/2.15  
% 5.67/2.15  Simplification rules
% 5.67/2.15  ----------------------
% 5.67/2.15  #Subsume      : 349
% 5.67/2.15  #Demod        : 100
% 5.67/2.15  #Tautology    : 76
% 5.67/2.15  #SimpNegUnit  : 182
% 5.67/2.15  #BackRed      : 7
% 5.67/2.15  
% 5.67/2.15  #Partial instantiations: 0
% 5.67/2.15  #Strategies tried      : 1
% 5.67/2.15  
% 5.67/2.15  Timing (in seconds)
% 5.67/2.15  ----------------------
% 5.67/2.15  Preprocessing        : 0.33
% 5.67/2.15  Parsing              : 0.17
% 5.67/2.16  CNF conversion       : 0.03
% 5.67/2.16  Main loop            : 0.96
% 5.67/2.16  Inferencing          : 0.35
% 5.67/2.16  Reduction            : 0.24
% 5.67/2.16  Demodulation         : 0.14
% 5.67/2.16  BG Simplification    : 0.04
% 5.67/2.16  Subsumption          : 0.25
% 5.67/2.16  Abstraction          : 0.04
% 5.67/2.16  MUC search           : 0.00
% 5.67/2.16  Cooper               : 0.00
% 5.67/2.16  Total                : 1.36
% 5.67/2.16  Index Insertion      : 0.00
% 5.67/2.16  Index Deletion       : 0.00
% 5.67/2.16  Index Matching       : 0.00
% 5.67/2.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
