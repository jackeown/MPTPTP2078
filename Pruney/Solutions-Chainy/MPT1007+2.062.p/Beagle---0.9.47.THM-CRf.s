%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:19 EST 2020

% Result     : Theorem 5.86s
% Output     : CNFRefutation 6.32s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 201 expanded)
%              Number of leaves         :   38 (  88 expanded)
%              Depth                    :   12
%              Number of atoms          :  148 ( 543 expanded)
%              Number of equality atoms :   27 ( 104 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_45,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_36,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_130,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_106,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_76,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
    <=> ( A = C
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_118,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(c_18,plain,(
    ! [A_13] : m1_subset_1('#skF_1'(A_13),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_8] : ~ v1_xboole_0(k1_tarski(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_95,plain,(
    ! [C_69,A_70,B_71] :
      ( v1_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_103,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_95])).

tff(c_50,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_38,plain,(
    ! [A_31] :
      ( r2_hidden('#skF_2'(A_31),A_31)
      | k1_xboole_0 = A_31 ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_203,plain,(
    ! [B_104,A_105] :
      ( r2_hidden(k4_tarski(B_104,k1_funct_1(A_105,B_104)),A_105)
      | ~ r2_hidden(B_104,k1_relat_1(A_105))
      | ~ v1_funct_1(A_105)
      | ~ v1_relat_1(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_20,plain,(
    ! [C_18,A_15,B_16] :
      ( r2_hidden(C_18,A_15)
      | ~ r2_hidden(C_18,B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1265,plain,(
    ! [B_197,A_198,A_199] :
      ( r2_hidden(k4_tarski(B_197,k1_funct_1(A_198,B_197)),A_199)
      | ~ m1_subset_1(A_198,k1_zfmisc_1(A_199))
      | ~ r2_hidden(B_197,k1_relat_1(A_198))
      | ~ v1_funct_1(A_198)
      | ~ v1_relat_1(A_198) ) ),
    inference(resolution,[status(thm)],[c_203,c_20])).

tff(c_16,plain,(
    ! [C_11,A_9,B_10,D_12] :
      ( C_11 = A_9
      | ~ r2_hidden(k4_tarski(A_9,B_10),k2_zfmisc_1(k1_tarski(C_11),D_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1327,plain,(
    ! [C_203,B_204,A_205,D_206] :
      ( C_203 = B_204
      | ~ m1_subset_1(A_205,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_203),D_206)))
      | ~ r2_hidden(B_204,k1_relat_1(A_205))
      | ~ v1_funct_1(A_205)
      | ~ v1_relat_1(A_205) ) ),
    inference(resolution,[status(thm)],[c_1265,c_16])).

tff(c_1329,plain,(
    ! [B_204] :
      ( B_204 = '#skF_3'
      | ~ r2_hidden(B_204,k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_1327])).

tff(c_1339,plain,(
    ! [B_207] :
      ( B_207 = '#skF_3'
      | ~ r2_hidden(B_207,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_50,c_1329])).

tff(c_1406,plain,
    ( '#skF_2'(k1_relat_1('#skF_5')) = '#skF_3'
    | k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_1339])).

tff(c_1447,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1406])).

tff(c_195,plain,(
    ! [A_102,B_103] :
      ( k1_funct_1(A_102,B_103) = k1_xboole_0
      | r2_hidden(B_103,k1_relat_1(A_102))
      | ~ v1_funct_1(A_102)
      | ~ v1_relat_1(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_32,plain,(
    ! [B_27,A_26] :
      ( ~ r1_tarski(B_27,A_26)
      | ~ r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_202,plain,(
    ! [A_102,B_103] :
      ( ~ r1_tarski(k1_relat_1(A_102),B_103)
      | k1_funct_1(A_102,B_103) = k1_xboole_0
      | ~ v1_funct_1(A_102)
      | ~ v1_relat_1(A_102) ) ),
    inference(resolution,[status(thm)],[c_195,c_32])).

tff(c_1456,plain,(
    ! [B_103] :
      ( ~ r1_tarski(k1_xboole_0,B_103)
      | k1_funct_1('#skF_5',B_103) = k1_xboole_0
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1447,c_202])).

tff(c_1467,plain,(
    ! [B_103] : k1_funct_1('#skF_5',B_103) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_50,c_2,c_1456])).

tff(c_42,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1473,plain,(
    ~ r2_hidden(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1467,c_42])).

tff(c_48,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( r2_hidden(A_19,B_20)
      | v1_xboole_0(B_20)
      | ~ m1_subset_1(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_400,plain,(
    ! [D_140,C_141,B_142,A_143] :
      ( r2_hidden(k1_funct_1(D_140,C_141),B_142)
      | k1_xboole_0 = B_142
      | ~ r2_hidden(C_141,A_143)
      | ~ m1_subset_1(D_140,k1_zfmisc_1(k2_zfmisc_1(A_143,B_142)))
      | ~ v1_funct_2(D_140,A_143,B_142)
      | ~ v1_funct_1(D_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1820,plain,(
    ! [D_232,A_233,B_234,B_235] :
      ( r2_hidden(k1_funct_1(D_232,A_233),B_234)
      | k1_xboole_0 = B_234
      | ~ m1_subset_1(D_232,k1_zfmisc_1(k2_zfmisc_1(B_235,B_234)))
      | ~ v1_funct_2(D_232,B_235,B_234)
      | ~ v1_funct_1(D_232)
      | v1_xboole_0(B_235)
      | ~ m1_subset_1(A_233,B_235) ) ),
    inference(resolution,[status(thm)],[c_22,c_400])).

tff(c_1822,plain,(
    ! [A_233] :
      ( r2_hidden(k1_funct_1('#skF_5',A_233),'#skF_4')
      | k1_xboole_0 = '#skF_4'
      | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0(k1_tarski('#skF_3'))
      | ~ m1_subset_1(A_233,k1_tarski('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_46,c_1820])).

tff(c_1828,plain,(
    ! [A_233] :
      ( r2_hidden(k1_xboole_0,'#skF_4')
      | k1_xboole_0 = '#skF_4'
      | v1_xboole_0(k1_tarski('#skF_3'))
      | ~ m1_subset_1(A_233,k1_tarski('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_1467,c_1822])).

tff(c_1831,plain,(
    ! [A_236] : ~ m1_subset_1(A_236,k1_tarski('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_44,c_1473,c_1828])).

tff(c_1836,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_18,c_1831])).

tff(c_1838,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1406])).

tff(c_1837,plain,(
    '#skF_2'(k1_relat_1('#skF_5')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1406])).

tff(c_1862,plain,
    ( r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1837,c_38])).

tff(c_1872,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_1838,c_1862])).

tff(c_14,plain,(
    ! [B_10,D_12,A_9,C_11] :
      ( r2_hidden(B_10,D_12)
      | ~ r2_hidden(k4_tarski(A_9,B_10),k2_zfmisc_1(k1_tarski(C_11),D_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_3984,plain,(
    ! [A_366,B_367,D_368,C_369] :
      ( r2_hidden(k1_funct_1(A_366,B_367),D_368)
      | ~ m1_subset_1(A_366,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_369),D_368)))
      | ~ r2_hidden(B_367,k1_relat_1(A_366))
      | ~ v1_funct_1(A_366)
      | ~ v1_relat_1(A_366) ) ),
    inference(resolution,[status(thm)],[c_1265,c_14])).

tff(c_3986,plain,(
    ! [B_367] :
      ( r2_hidden(k1_funct_1('#skF_5',B_367),'#skF_4')
      | ~ r2_hidden(B_367,k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_3984])).

tff(c_4046,plain,(
    ! [B_370] :
      ( r2_hidden(k1_funct_1('#skF_5',B_370),'#skF_4')
      | ~ r2_hidden(B_370,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_50,c_3986])).

tff(c_4054,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_4046,c_42])).

tff(c_4060,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1872,c_4054])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:50:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.86/2.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.32/2.25  
% 6.32/2.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.32/2.25  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 6.32/2.25  
% 6.32/2.25  %Foreground sorts:
% 6.32/2.25  
% 6.32/2.25  
% 6.32/2.25  %Background operators:
% 6.32/2.25  
% 6.32/2.25  
% 6.32/2.25  %Foreground operators:
% 6.32/2.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.32/2.25  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.32/2.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.32/2.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.32/2.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.32/2.25  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.32/2.25  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.32/2.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.32/2.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.32/2.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.32/2.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.32/2.25  tff('#skF_5', type, '#skF_5': $i).
% 6.32/2.25  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.32/2.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.32/2.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.32/2.25  tff('#skF_3', type, '#skF_3': $i).
% 6.32/2.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.32/2.25  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.32/2.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.32/2.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.32/2.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.32/2.25  tff('#skF_4', type, '#skF_4': $i).
% 6.32/2.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.32/2.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.32/2.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.32/2.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.32/2.25  
% 6.32/2.27  tff(f_45, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 6.32/2.27  tff(f_36, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 6.32/2.27  tff(f_130, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 6.32/2.27  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.32/2.27  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.32/2.27  tff(f_106, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_mcart_1)).
% 6.32/2.27  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 6.32/2.27  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 6.32/2.27  tff(f_42, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 6.32/2.27  tff(f_81, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.32/2.27  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 6.32/2.27  tff(f_118, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 6.32/2.27  tff(c_18, plain, (![A_13]: (m1_subset_1('#skF_1'(A_13), A_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.32/2.27  tff(c_10, plain, (![A_8]: (~v1_xboole_0(k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.32/2.27  tff(c_44, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.32/2.27  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.32/2.27  tff(c_95, plain, (![C_69, A_70, B_71]: (v1_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.32/2.27  tff(c_103, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_95])).
% 6.32/2.27  tff(c_50, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.32/2.27  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.32/2.27  tff(c_38, plain, (![A_31]: (r2_hidden('#skF_2'(A_31), A_31) | k1_xboole_0=A_31)), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.32/2.27  tff(c_203, plain, (![B_104, A_105]: (r2_hidden(k4_tarski(B_104, k1_funct_1(A_105, B_104)), A_105) | ~r2_hidden(B_104, k1_relat_1(A_105)) | ~v1_funct_1(A_105) | ~v1_relat_1(A_105))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.32/2.27  tff(c_20, plain, (![C_18, A_15, B_16]: (r2_hidden(C_18, A_15) | ~r2_hidden(C_18, B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.32/2.27  tff(c_1265, plain, (![B_197, A_198, A_199]: (r2_hidden(k4_tarski(B_197, k1_funct_1(A_198, B_197)), A_199) | ~m1_subset_1(A_198, k1_zfmisc_1(A_199)) | ~r2_hidden(B_197, k1_relat_1(A_198)) | ~v1_funct_1(A_198) | ~v1_relat_1(A_198))), inference(resolution, [status(thm)], [c_203, c_20])).
% 6.32/2.27  tff(c_16, plain, (![C_11, A_9, B_10, D_12]: (C_11=A_9 | ~r2_hidden(k4_tarski(A_9, B_10), k2_zfmisc_1(k1_tarski(C_11), D_12)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.32/2.27  tff(c_1327, plain, (![C_203, B_204, A_205, D_206]: (C_203=B_204 | ~m1_subset_1(A_205, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_203), D_206))) | ~r2_hidden(B_204, k1_relat_1(A_205)) | ~v1_funct_1(A_205) | ~v1_relat_1(A_205))), inference(resolution, [status(thm)], [c_1265, c_16])).
% 6.32/2.27  tff(c_1329, plain, (![B_204]: (B_204='#skF_3' | ~r2_hidden(B_204, k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_46, c_1327])).
% 6.32/2.27  tff(c_1339, plain, (![B_207]: (B_207='#skF_3' | ~r2_hidden(B_207, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_50, c_1329])).
% 6.32/2.27  tff(c_1406, plain, ('#skF_2'(k1_relat_1('#skF_5'))='#skF_3' | k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_1339])).
% 6.32/2.27  tff(c_1447, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1406])).
% 6.32/2.27  tff(c_195, plain, (![A_102, B_103]: (k1_funct_1(A_102, B_103)=k1_xboole_0 | r2_hidden(B_103, k1_relat_1(A_102)) | ~v1_funct_1(A_102) | ~v1_relat_1(A_102))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.32/2.27  tff(c_32, plain, (![B_27, A_26]: (~r1_tarski(B_27, A_26) | ~r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.32/2.27  tff(c_202, plain, (![A_102, B_103]: (~r1_tarski(k1_relat_1(A_102), B_103) | k1_funct_1(A_102, B_103)=k1_xboole_0 | ~v1_funct_1(A_102) | ~v1_relat_1(A_102))), inference(resolution, [status(thm)], [c_195, c_32])).
% 6.32/2.27  tff(c_1456, plain, (![B_103]: (~r1_tarski(k1_xboole_0, B_103) | k1_funct_1('#skF_5', B_103)=k1_xboole_0 | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1447, c_202])).
% 6.32/2.27  tff(c_1467, plain, (![B_103]: (k1_funct_1('#skF_5', B_103)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_103, c_50, c_2, c_1456])).
% 6.32/2.27  tff(c_42, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.32/2.27  tff(c_1473, plain, (~r2_hidden(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1467, c_42])).
% 6.32/2.27  tff(c_48, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.32/2.27  tff(c_22, plain, (![A_19, B_20]: (r2_hidden(A_19, B_20) | v1_xboole_0(B_20) | ~m1_subset_1(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.32/2.27  tff(c_400, plain, (![D_140, C_141, B_142, A_143]: (r2_hidden(k1_funct_1(D_140, C_141), B_142) | k1_xboole_0=B_142 | ~r2_hidden(C_141, A_143) | ~m1_subset_1(D_140, k1_zfmisc_1(k2_zfmisc_1(A_143, B_142))) | ~v1_funct_2(D_140, A_143, B_142) | ~v1_funct_1(D_140))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.32/2.27  tff(c_1820, plain, (![D_232, A_233, B_234, B_235]: (r2_hidden(k1_funct_1(D_232, A_233), B_234) | k1_xboole_0=B_234 | ~m1_subset_1(D_232, k1_zfmisc_1(k2_zfmisc_1(B_235, B_234))) | ~v1_funct_2(D_232, B_235, B_234) | ~v1_funct_1(D_232) | v1_xboole_0(B_235) | ~m1_subset_1(A_233, B_235))), inference(resolution, [status(thm)], [c_22, c_400])).
% 6.32/2.27  tff(c_1822, plain, (![A_233]: (r2_hidden(k1_funct_1('#skF_5', A_233), '#skF_4') | k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0(k1_tarski('#skF_3')) | ~m1_subset_1(A_233, k1_tarski('#skF_3')))), inference(resolution, [status(thm)], [c_46, c_1820])).
% 6.32/2.27  tff(c_1828, plain, (![A_233]: (r2_hidden(k1_xboole_0, '#skF_4') | k1_xboole_0='#skF_4' | v1_xboole_0(k1_tarski('#skF_3')) | ~m1_subset_1(A_233, k1_tarski('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_1467, c_1822])).
% 6.32/2.27  tff(c_1831, plain, (![A_236]: (~m1_subset_1(A_236, k1_tarski('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_10, c_44, c_1473, c_1828])).
% 6.32/2.27  tff(c_1836, plain, $false, inference(resolution, [status(thm)], [c_18, c_1831])).
% 6.32/2.27  tff(c_1838, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1406])).
% 6.32/2.27  tff(c_1837, plain, ('#skF_2'(k1_relat_1('#skF_5'))='#skF_3'), inference(splitRight, [status(thm)], [c_1406])).
% 6.32/2.27  tff(c_1862, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5')) | k1_relat_1('#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1837, c_38])).
% 6.32/2.27  tff(c_1872, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_1838, c_1862])).
% 6.32/2.27  tff(c_14, plain, (![B_10, D_12, A_9, C_11]: (r2_hidden(B_10, D_12) | ~r2_hidden(k4_tarski(A_9, B_10), k2_zfmisc_1(k1_tarski(C_11), D_12)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.32/2.27  tff(c_3984, plain, (![A_366, B_367, D_368, C_369]: (r2_hidden(k1_funct_1(A_366, B_367), D_368) | ~m1_subset_1(A_366, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_369), D_368))) | ~r2_hidden(B_367, k1_relat_1(A_366)) | ~v1_funct_1(A_366) | ~v1_relat_1(A_366))), inference(resolution, [status(thm)], [c_1265, c_14])).
% 6.32/2.27  tff(c_3986, plain, (![B_367]: (r2_hidden(k1_funct_1('#skF_5', B_367), '#skF_4') | ~r2_hidden(B_367, k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_46, c_3984])).
% 6.32/2.27  tff(c_4046, plain, (![B_370]: (r2_hidden(k1_funct_1('#skF_5', B_370), '#skF_4') | ~r2_hidden(B_370, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_50, c_3986])).
% 6.32/2.27  tff(c_4054, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_4046, c_42])).
% 6.32/2.27  tff(c_4060, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1872, c_4054])).
% 6.32/2.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.32/2.27  
% 6.32/2.27  Inference rules
% 6.32/2.27  ----------------------
% 6.32/2.27  #Ref     : 0
% 6.32/2.27  #Sup     : 955
% 6.32/2.27  #Fact    : 0
% 6.32/2.27  #Define  : 0
% 6.32/2.27  #Split   : 22
% 6.32/2.27  #Chain   : 0
% 6.32/2.27  #Close   : 0
% 6.32/2.27  
% 6.32/2.27  Ordering : KBO
% 6.32/2.27  
% 6.32/2.27  Simplification rules
% 6.32/2.27  ----------------------
% 6.32/2.27  #Subsume      : 142
% 6.32/2.27  #Demod        : 655
% 6.32/2.27  #Tautology    : 252
% 6.32/2.27  #SimpNegUnit  : 15
% 6.32/2.27  #BackRed      : 87
% 6.32/2.27  
% 6.32/2.27  #Partial instantiations: 0
% 6.32/2.27  #Strategies tried      : 1
% 6.32/2.27  
% 6.32/2.27  Timing (in seconds)
% 6.32/2.27  ----------------------
% 6.32/2.27  Preprocessing        : 0.34
% 6.32/2.27  Parsing              : 0.18
% 6.32/2.27  CNF conversion       : 0.02
% 6.32/2.27  Main loop            : 1.11
% 6.32/2.27  Inferencing          : 0.31
% 6.32/2.27  Reduction            : 0.34
% 6.32/2.27  Demodulation         : 0.23
% 6.32/2.27  BG Simplification    : 0.04
% 6.32/2.27  Subsumption          : 0.32
% 6.32/2.27  Abstraction          : 0.05
% 6.32/2.27  MUC search           : 0.00
% 6.32/2.27  Cooper               : 0.00
% 6.32/2.27  Total                : 1.48
% 6.32/2.27  Index Insertion      : 0.00
% 6.32/2.27  Index Deletion       : 0.00
% 6.32/2.27  Index Matching       : 0.00
% 6.32/2.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
