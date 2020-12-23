%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:46 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 4.12s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 110 expanded)
%              Number of leaves         :   36 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :  117 ( 190 expanded)
%              Number of equality atoms :   20 (  25 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_3 > #skF_5 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_94,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_134,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_55,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

tff(f_123,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_96,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_57,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_53,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_110,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ! [C] :
              ( m1_subset_1(C,A)
             => ( ~ r2_hidden(C,B)
               => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_38,plain,(
    ! [A_31] : m1_subset_1('#skF_4'(A_31),A_31) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_16,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1950,plain,(
    ! [A_231,B_232] :
      ( r2_hidden('#skF_3'(A_231,B_232),B_232)
      | ~ r2_hidden(A_231,B_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_48,plain,(
    ! [B_47,A_46] :
      ( ~ r1_tarski(B_47,A_46)
      | ~ r2_hidden(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_2050,plain,(
    ! [B_249,A_250] :
      ( ~ r1_tarski(B_249,'#skF_3'(A_250,B_249))
      | ~ r2_hidden(A_250,B_249) ) ),
    inference(resolution,[status(thm)],[c_1950,c_48])).

tff(c_2055,plain,(
    ! [A_250] : ~ r2_hidden(A_250,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_2050])).

tff(c_40,plain,(
    ! [A_33] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_18,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_14,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2002,plain,(
    ! [A_241,B_242] : k5_xboole_0(A_241,k3_xboole_0(A_241,B_242)) = k4_xboole_0(A_241,B_242) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2011,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = k4_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_2002])).

tff(c_2014,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2011])).

tff(c_2169,plain,(
    ! [A_268,B_269] :
      ( k4_xboole_0(A_268,B_269) = k3_subset_1(A_268,B_269)
      | ~ m1_subset_1(B_269,k1_zfmisc_1(A_268)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2180,plain,(
    ! [A_33] : k4_xboole_0(A_33,k1_xboole_0) = k3_subset_1(A_33,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_40,c_2169])).

tff(c_2188,plain,(
    ! [A_33] : k3_subset_1(A_33,k1_xboole_0) = A_33 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2014,c_2180])).

tff(c_2253,plain,(
    ! [C_278,A_279,B_280] :
      ( r2_hidden(C_278,k3_subset_1(A_279,B_280))
      | r2_hidden(C_278,B_280)
      | ~ m1_subset_1(C_278,A_279)
      | ~ m1_subset_1(B_280,k1_zfmisc_1(A_279))
      | k1_xboole_0 = A_279 ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2265,plain,(
    ! [C_278,A_33] :
      ( r2_hidden(C_278,A_33)
      | r2_hidden(C_278,k1_xboole_0)
      | ~ m1_subset_1(C_278,A_33)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_33))
      | k1_xboole_0 = A_33 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2188,c_2253])).

tff(c_2270,plain,(
    ! [C_278,A_33] :
      ( r2_hidden(C_278,A_33)
      | r2_hidden(C_278,k1_xboole_0)
      | ~ m1_subset_1(C_278,A_33)
      | k1_xboole_0 = A_33 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2265])).

tff(c_2272,plain,(
    ! [C_281,A_282] :
      ( r2_hidden(C_281,A_282)
      | ~ m1_subset_1(C_281,A_282)
      | k1_xboole_0 = A_282 ) ),
    inference(negUnitSimplification,[status(thm)],[c_2055,c_2270])).

tff(c_221,plain,(
    ! [A_85,B_86] :
      ( r2_hidden('#skF_2'(A_85,B_86),B_86)
      | r1_xboole_0(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_244,plain,(
    ! [B_88,A_89] :
      ( ~ v1_xboole_0(B_88)
      | r1_xboole_0(A_89,B_88) ) ),
    inference(resolution,[status(thm)],[c_221,c_2])).

tff(c_75,plain,(
    ! [A_60] :
      ( v1_xboole_0(A_60)
      | r2_hidden('#skF_1'(A_60),A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    ! [B_49] :
      ( ~ r1_xboole_0(B_49,'#skF_5')
      | ~ r2_hidden(B_49,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_86,plain,
    ( ~ r1_xboole_0('#skF_1'('#skF_5'),'#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_75,c_50])).

tff(c_89,plain,(
    ~ r1_xboole_0('#skF_1'('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_252,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_244,c_89])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_533,plain,(
    ! [D_128,A_129,B_130] :
      ( ~ r2_hidden(D_128,'#skF_3'(A_129,B_130))
      | ~ r2_hidden(D_128,B_130)
      | ~ r2_hidden(A_129,B_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1786,plain,(
    ! [A_207,B_208,B_209] :
      ( ~ r2_hidden('#skF_2'('#skF_3'(A_207,B_208),B_209),B_208)
      | ~ r2_hidden(A_207,B_208)
      | r1_xboole_0('#skF_3'(A_207,B_208),B_209) ) ),
    inference(resolution,[status(thm)],[c_10,c_533])).

tff(c_1815,plain,(
    ! [A_211,B_212] :
      ( ~ r2_hidden(A_211,B_212)
      | r1_xboole_0('#skF_3'(A_211,B_212),B_212) ) ),
    inference(resolution,[status(thm)],[c_8,c_1786])).

tff(c_144,plain,(
    ! [A_73,B_74] :
      ( r2_hidden('#skF_3'(A_73,B_74),B_74)
      | ~ r2_hidden(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_155,plain,(
    ! [A_73] :
      ( ~ r1_xboole_0('#skF_3'(A_73,'#skF_5'),'#skF_5')
      | ~ r2_hidden(A_73,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_144,c_50])).

tff(c_1829,plain,(
    ! [A_213] : ~ r2_hidden(A_213,'#skF_5') ),
    inference(resolution,[status(thm)],[c_1815,c_155])).

tff(c_1853,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_1829])).

tff(c_1866,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_252,c_1853])).

tff(c_1867,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_1909,plain,(
    ! [A_224,B_225] :
      ( r2_hidden('#skF_2'(A_224,B_225),B_225)
      | r1_xboole_0(A_224,B_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1924,plain,(
    ! [B_227,A_228] :
      ( ~ v1_xboole_0(B_227)
      | r1_xboole_0(A_228,B_227) ) ),
    inference(resolution,[status(thm)],[c_1909,c_2])).

tff(c_1920,plain,(
    ! [A_224] :
      ( ~ r1_xboole_0('#skF_2'(A_224,'#skF_5'),'#skF_5')
      | r1_xboole_0(A_224,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1909,c_50])).

tff(c_1927,plain,(
    ! [A_224] :
      ( r1_xboole_0(A_224,'#skF_5')
      | ~ v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1924,c_1920])).

tff(c_1930,plain,(
    ! [A_224] : r1_xboole_0(A_224,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1867,c_1927])).

tff(c_1935,plain,(
    ! [B_49] : ~ r2_hidden(B_49,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1930,c_50])).

tff(c_2291,plain,(
    ! [C_281] :
      ( ~ m1_subset_1(C_281,'#skF_5')
      | k1_xboole_0 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_2272,c_1935])).

tff(c_2308,plain,(
    ! [C_283] : ~ m1_subset_1(C_283,'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2291])).

tff(c_2338,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_38,c_2308])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:55:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.95/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.12/1.68  
% 4.12/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.12/1.68  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_3 > #skF_5 > #skF_2
% 4.12/1.68  
% 4.12/1.68  %Foreground sorts:
% 4.12/1.68  
% 4.12/1.68  
% 4.12/1.68  %Background operators:
% 4.12/1.68  
% 4.12/1.68  
% 4.12/1.68  %Foreground operators:
% 4.12/1.68  tff('#skF_4', type, '#skF_4': $i > $i).
% 4.12/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.12/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.12/1.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.12/1.68  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.12/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.12/1.68  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.12/1.68  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.12/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.12/1.68  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.12/1.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.12/1.68  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.12/1.68  tff('#skF_5', type, '#skF_5': $i).
% 4.12/1.68  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.12/1.68  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.12/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.12/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.12/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.12/1.68  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.12/1.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.12/1.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.12/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.12/1.68  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.12/1.68  
% 4.12/1.70  tff(f_94, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 4.12/1.70  tff(f_134, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 4.12/1.70  tff(f_55, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.12/1.70  tff(f_74, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 4.12/1.70  tff(f_123, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.12/1.70  tff(f_96, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.12/1.70  tff(f_57, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.12/1.70  tff(f_53, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 4.12/1.70  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.12/1.70  tff(f_91, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.12/1.70  tff(f_110, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_subset_1)).
% 4.12/1.70  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.12/1.70  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.12/1.70  tff(c_38, plain, (![A_31]: (m1_subset_1('#skF_4'(A_31), A_31))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.12/1.70  tff(c_52, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.12/1.70  tff(c_16, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.12/1.70  tff(c_1950, plain, (![A_231, B_232]: (r2_hidden('#skF_3'(A_231, B_232), B_232) | ~r2_hidden(A_231, B_232))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.12/1.70  tff(c_48, plain, (![B_47, A_46]: (~r1_tarski(B_47, A_46) | ~r2_hidden(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.12/1.70  tff(c_2050, plain, (![B_249, A_250]: (~r1_tarski(B_249, '#skF_3'(A_250, B_249)) | ~r2_hidden(A_250, B_249))), inference(resolution, [status(thm)], [c_1950, c_48])).
% 4.12/1.70  tff(c_2055, plain, (![A_250]: (~r2_hidden(A_250, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_2050])).
% 4.12/1.70  tff(c_40, plain, (![A_33]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.12/1.70  tff(c_18, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.12/1.70  tff(c_14, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.12/1.70  tff(c_2002, plain, (![A_241, B_242]: (k5_xboole_0(A_241, k3_xboole_0(A_241, B_242))=k4_xboole_0(A_241, B_242))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.12/1.70  tff(c_2011, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=k4_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_2002])).
% 4.12/1.70  tff(c_2014, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2011])).
% 4.12/1.70  tff(c_2169, plain, (![A_268, B_269]: (k4_xboole_0(A_268, B_269)=k3_subset_1(A_268, B_269) | ~m1_subset_1(B_269, k1_zfmisc_1(A_268)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.12/1.70  tff(c_2180, plain, (![A_33]: (k4_xboole_0(A_33, k1_xboole_0)=k3_subset_1(A_33, k1_xboole_0))), inference(resolution, [status(thm)], [c_40, c_2169])).
% 4.12/1.70  tff(c_2188, plain, (![A_33]: (k3_subset_1(A_33, k1_xboole_0)=A_33)), inference(demodulation, [status(thm), theory('equality')], [c_2014, c_2180])).
% 4.12/1.70  tff(c_2253, plain, (![C_278, A_279, B_280]: (r2_hidden(C_278, k3_subset_1(A_279, B_280)) | r2_hidden(C_278, B_280) | ~m1_subset_1(C_278, A_279) | ~m1_subset_1(B_280, k1_zfmisc_1(A_279)) | k1_xboole_0=A_279)), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.12/1.70  tff(c_2265, plain, (![C_278, A_33]: (r2_hidden(C_278, A_33) | r2_hidden(C_278, k1_xboole_0) | ~m1_subset_1(C_278, A_33) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_33)) | k1_xboole_0=A_33)), inference(superposition, [status(thm), theory('equality')], [c_2188, c_2253])).
% 4.12/1.70  tff(c_2270, plain, (![C_278, A_33]: (r2_hidden(C_278, A_33) | r2_hidden(C_278, k1_xboole_0) | ~m1_subset_1(C_278, A_33) | k1_xboole_0=A_33)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2265])).
% 4.12/1.70  tff(c_2272, plain, (![C_281, A_282]: (r2_hidden(C_281, A_282) | ~m1_subset_1(C_281, A_282) | k1_xboole_0=A_282)), inference(negUnitSimplification, [status(thm)], [c_2055, c_2270])).
% 4.12/1.70  tff(c_221, plain, (![A_85, B_86]: (r2_hidden('#skF_2'(A_85, B_86), B_86) | r1_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.12/1.70  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.12/1.70  tff(c_244, plain, (![B_88, A_89]: (~v1_xboole_0(B_88) | r1_xboole_0(A_89, B_88))), inference(resolution, [status(thm)], [c_221, c_2])).
% 4.12/1.70  tff(c_75, plain, (![A_60]: (v1_xboole_0(A_60) | r2_hidden('#skF_1'(A_60), A_60))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.12/1.70  tff(c_50, plain, (![B_49]: (~r1_xboole_0(B_49, '#skF_5') | ~r2_hidden(B_49, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.12/1.70  tff(c_86, plain, (~r1_xboole_0('#skF_1'('#skF_5'), '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_75, c_50])).
% 4.12/1.70  tff(c_89, plain, (~r1_xboole_0('#skF_1'('#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_86])).
% 4.12/1.70  tff(c_252, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_244, c_89])).
% 4.12/1.70  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.12/1.70  tff(c_8, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.12/1.70  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.12/1.70  tff(c_533, plain, (![D_128, A_129, B_130]: (~r2_hidden(D_128, '#skF_3'(A_129, B_130)) | ~r2_hidden(D_128, B_130) | ~r2_hidden(A_129, B_130))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.12/1.70  tff(c_1786, plain, (![A_207, B_208, B_209]: (~r2_hidden('#skF_2'('#skF_3'(A_207, B_208), B_209), B_208) | ~r2_hidden(A_207, B_208) | r1_xboole_0('#skF_3'(A_207, B_208), B_209))), inference(resolution, [status(thm)], [c_10, c_533])).
% 4.12/1.70  tff(c_1815, plain, (![A_211, B_212]: (~r2_hidden(A_211, B_212) | r1_xboole_0('#skF_3'(A_211, B_212), B_212))), inference(resolution, [status(thm)], [c_8, c_1786])).
% 4.12/1.70  tff(c_144, plain, (![A_73, B_74]: (r2_hidden('#skF_3'(A_73, B_74), B_74) | ~r2_hidden(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.12/1.70  tff(c_155, plain, (![A_73]: (~r1_xboole_0('#skF_3'(A_73, '#skF_5'), '#skF_5') | ~r2_hidden(A_73, '#skF_5'))), inference(resolution, [status(thm)], [c_144, c_50])).
% 4.12/1.70  tff(c_1829, plain, (![A_213]: (~r2_hidden(A_213, '#skF_5'))), inference(resolution, [status(thm)], [c_1815, c_155])).
% 4.12/1.70  tff(c_1853, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_1829])).
% 4.12/1.70  tff(c_1866, plain, $false, inference(negUnitSimplification, [status(thm)], [c_252, c_1853])).
% 4.12/1.70  tff(c_1867, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_86])).
% 4.12/1.70  tff(c_1909, plain, (![A_224, B_225]: (r2_hidden('#skF_2'(A_224, B_225), B_225) | r1_xboole_0(A_224, B_225))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.12/1.70  tff(c_1924, plain, (![B_227, A_228]: (~v1_xboole_0(B_227) | r1_xboole_0(A_228, B_227))), inference(resolution, [status(thm)], [c_1909, c_2])).
% 4.12/1.70  tff(c_1920, plain, (![A_224]: (~r1_xboole_0('#skF_2'(A_224, '#skF_5'), '#skF_5') | r1_xboole_0(A_224, '#skF_5'))), inference(resolution, [status(thm)], [c_1909, c_50])).
% 4.12/1.70  tff(c_1927, plain, (![A_224]: (r1_xboole_0(A_224, '#skF_5') | ~v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_1924, c_1920])).
% 4.12/1.70  tff(c_1930, plain, (![A_224]: (r1_xboole_0(A_224, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1867, c_1927])).
% 4.12/1.70  tff(c_1935, plain, (![B_49]: (~r2_hidden(B_49, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1930, c_50])).
% 4.12/1.70  tff(c_2291, plain, (![C_281]: (~m1_subset_1(C_281, '#skF_5') | k1_xboole_0='#skF_5')), inference(resolution, [status(thm)], [c_2272, c_1935])).
% 4.12/1.70  tff(c_2308, plain, (![C_283]: (~m1_subset_1(C_283, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_52, c_2291])).
% 4.12/1.70  tff(c_2338, plain, $false, inference(resolution, [status(thm)], [c_38, c_2308])).
% 4.12/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.12/1.70  
% 4.12/1.70  Inference rules
% 4.12/1.70  ----------------------
% 4.12/1.70  #Ref     : 0
% 4.12/1.70  #Sup     : 488
% 4.12/1.70  #Fact    : 0
% 4.12/1.70  #Define  : 0
% 4.12/1.70  #Split   : 3
% 4.12/1.70  #Chain   : 0
% 4.12/1.70  #Close   : 0
% 4.12/1.70  
% 4.12/1.70  Ordering : KBO
% 4.12/1.70  
% 4.12/1.70  Simplification rules
% 4.12/1.70  ----------------------
% 4.12/1.70  #Subsume      : 117
% 4.12/1.70  #Demod        : 114
% 4.12/1.70  #Tautology    : 142
% 4.12/1.70  #SimpNegUnit  : 20
% 4.12/1.70  #BackRed      : 1
% 4.12/1.70  
% 4.12/1.70  #Partial instantiations: 0
% 4.12/1.70  #Strategies tried      : 1
% 4.12/1.70  
% 4.12/1.70  Timing (in seconds)
% 4.12/1.70  ----------------------
% 4.12/1.70  Preprocessing        : 0.33
% 4.12/1.70  Parsing              : 0.17
% 4.12/1.70  CNF conversion       : 0.02
% 4.12/1.70  Main loop            : 0.61
% 4.12/1.70  Inferencing          : 0.23
% 4.12/1.70  Reduction            : 0.16
% 4.12/1.70  Demodulation         : 0.11
% 4.12/1.70  BG Simplification    : 0.03
% 4.12/1.70  Subsumption          : 0.13
% 4.12/1.70  Abstraction          : 0.03
% 4.12/1.70  MUC search           : 0.00
% 4.12/1.70  Cooper               : 0.00
% 4.12/1.70  Total                : 0.97
% 4.12/1.70  Index Insertion      : 0.00
% 4.12/1.70  Index Deletion       : 0.00
% 4.12/1.70  Index Matching       : 0.00
% 4.12/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
