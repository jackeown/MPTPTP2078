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
% DateTime   : Thu Dec  3 10:14:17 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :   78 (  88 expanded)
%              Number of leaves         :   43 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :   94 ( 132 expanded)
%              Number of equality atoms :   41 (  48 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_124,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_69,axiom,(
    ! [A,B,C,D,E,F,G,H,I] :
      ( I = k6_enumset1(A,B,C,D,E,F,G,H)
    <=> ! [J] :
          ( r2_hidden(J,I)
        <=> ~ ( J != A
              & J != B
              & J != C
              & J != D
              & J != E
              & J != F
              & J != G
              & J != H ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).

tff(c_96,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_119,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_123,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_96,c_119])).

tff(c_124,plain,(
    ! [C_63,B_64,A_65] :
      ( v5_relat_1(C_63,B_64)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_65,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_128,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_124])).

tff(c_100,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_191,plain,(
    ! [B_161,C_162,A_163] :
      ( r2_hidden(k1_funct_1(B_161,C_162),A_163)
      | ~ r2_hidden(C_162,k1_relat_1(B_161))
      | ~ v1_funct_1(B_161)
      | ~ v5_relat_1(B_161,A_163)
      | ~ v1_relat_1(B_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_92,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_194,plain,
    ( ~ r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_191,c_92])).

tff(c_197,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_128,c_100,c_194])).

tff(c_94,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_98,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_161,plain,(
    ! [A_141,B_142,C_143] :
      ( k1_relset_1(A_141,B_142,C_143) = k1_relat_1(C_143)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_165,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_96,c_161])).

tff(c_198,plain,(
    ! [B_164,A_165,C_166] :
      ( k1_xboole_0 = B_164
      | k1_relset_1(A_165,B_164,C_166) = A_165
      | ~ v1_funct_2(C_166,A_165,B_164)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_165,B_164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_201,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_198])).

tff(c_204,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_165,c_201])).

tff(c_205,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_204])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k2_enumset1(A_4,A_4,B_5,C_6) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9,D_10] : k3_enumset1(A_7,A_7,B_8,C_9,D_10) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [D_14,E_15,B_12,A_11,C_13] : k4_enumset1(A_11,A_11,B_12,C_13,D_14,E_15) = k3_enumset1(A_11,B_12,C_13,D_14,E_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [C_18,B_17,A_16,D_19,E_20,F_21] : k5_enumset1(A_16,A_16,B_17,C_18,D_19,E_20,F_21) = k4_enumset1(A_16,B_17,C_18,D_19,E_20,F_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_253,plain,(
    ! [C_171,A_170,F_173,D_175,G_174,B_176,E_172] : k6_enumset1(A_170,A_170,B_176,C_171,D_175,E_172,F_173,G_174) = k5_enumset1(A_170,B_176,C_171,D_175,E_172,F_173,G_174) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [G_35,H_36,E_33,J_40,A_29,D_32,C_31,B_30] : r2_hidden(J_40,k6_enumset1(A_29,B_30,C_31,D_32,E_33,J_40,G_35,H_36)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_286,plain,(
    ! [B_180,D_183,E_178,C_181,A_177,G_182,F_179] : r2_hidden(E_178,k5_enumset1(A_177,B_180,C_181,D_183,E_178,F_179,G_182)) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_22])).

tff(c_290,plain,(
    ! [D_188,F_184,B_185,A_187,E_186,C_189] : r2_hidden(D_188,k4_enumset1(A_187,B_185,C_189,D_188,E_186,F_184)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_286])).

tff(c_343,plain,(
    ! [A_200,C_199,E_203,D_202,B_201] : r2_hidden(C_199,k3_enumset1(A_200,B_201,C_199,D_202,E_203)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_290])).

tff(c_347,plain,(
    ! [B_204,A_205,C_206,D_207] : r2_hidden(B_204,k2_enumset1(A_205,B_204,C_206,D_207)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_343])).

tff(c_351,plain,(
    ! [A_208,B_209,C_210] : r2_hidden(A_208,k1_enumset1(A_208,B_209,C_210)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_347])).

tff(c_356,plain,(
    ! [A_220,B_221] : r2_hidden(A_220,k2_tarski(A_220,B_221)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_351])).

tff(c_360,plain,(
    ! [A_222] : r2_hidden(A_222,k1_tarski(A_222)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_356])).

tff(c_363,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_360])).

tff(c_365,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_363])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:03:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.93/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.37  
% 3.02/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.37  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.02/1.37  
% 3.02/1.37  %Foreground sorts:
% 3.02/1.37  
% 3.02/1.37  
% 3.02/1.37  %Background operators:
% 3.02/1.37  
% 3.02/1.37  
% 3.02/1.37  %Foreground operators:
% 3.02/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.02/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.02/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.02/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.02/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.02/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.02/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.02/1.37  tff('#skF_5', type, '#skF_5': $i).
% 3.02/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.02/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.02/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.02/1.37  tff('#skF_3', type, '#skF_3': $i).
% 3.02/1.37  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.02/1.37  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.02/1.37  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.02/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.02/1.37  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.02/1.37  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.02/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.02/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.02/1.37  tff('#skF_4', type, '#skF_4': $i).
% 3.02/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.02/1.37  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.02/1.37  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.02/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.02/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.02/1.37  
% 3.02/1.39  tff(f_124, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 3.02/1.39  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.02/1.39  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.02/1.39  tff(f_80, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 3.02/1.39  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.02/1.39  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.02/1.39  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.02/1.39  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.02/1.39  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.02/1.39  tff(f_33, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.02/1.39  tff(f_35, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 3.02/1.39  tff(f_37, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 3.02/1.39  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 3.02/1.39  tff(f_69, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_enumset1)).
% 3.02/1.39  tff(c_96, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.02/1.39  tff(c_119, plain, (![C_60, A_61, B_62]: (v1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.02/1.39  tff(c_123, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_96, c_119])).
% 3.02/1.39  tff(c_124, plain, (![C_63, B_64, A_65]: (v5_relat_1(C_63, B_64) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_65, B_64))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.02/1.39  tff(c_128, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_96, c_124])).
% 3.02/1.39  tff(c_100, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.02/1.39  tff(c_191, plain, (![B_161, C_162, A_163]: (r2_hidden(k1_funct_1(B_161, C_162), A_163) | ~r2_hidden(C_162, k1_relat_1(B_161)) | ~v1_funct_1(B_161) | ~v5_relat_1(B_161, A_163) | ~v1_relat_1(B_161))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.02/1.39  tff(c_92, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.02/1.39  tff(c_194, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_191, c_92])).
% 3.02/1.39  tff(c_197, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_128, c_100, c_194])).
% 3.02/1.39  tff(c_94, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.02/1.39  tff(c_98, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.02/1.39  tff(c_161, plain, (![A_141, B_142, C_143]: (k1_relset_1(A_141, B_142, C_143)=k1_relat_1(C_143) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.02/1.39  tff(c_165, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_96, c_161])).
% 3.02/1.39  tff(c_198, plain, (![B_164, A_165, C_166]: (k1_xboole_0=B_164 | k1_relset_1(A_165, B_164, C_166)=A_165 | ~v1_funct_2(C_166, A_165, B_164) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(A_165, B_164))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.02/1.39  tff(c_201, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_96, c_198])).
% 3.02/1.39  tff(c_204, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_165, c_201])).
% 3.02/1.39  tff(c_205, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_94, c_204])).
% 3.02/1.39  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.02/1.39  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.02/1.39  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.02/1.39  tff(c_8, plain, (![A_7, B_8, C_9, D_10]: (k3_enumset1(A_7, A_7, B_8, C_9, D_10)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.02/1.39  tff(c_10, plain, (![D_14, E_15, B_12, A_11, C_13]: (k4_enumset1(A_11, A_11, B_12, C_13, D_14, E_15)=k3_enumset1(A_11, B_12, C_13, D_14, E_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.02/1.39  tff(c_12, plain, (![C_18, B_17, A_16, D_19, E_20, F_21]: (k5_enumset1(A_16, A_16, B_17, C_18, D_19, E_20, F_21)=k4_enumset1(A_16, B_17, C_18, D_19, E_20, F_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.02/1.39  tff(c_253, plain, (![C_171, A_170, F_173, D_175, G_174, B_176, E_172]: (k6_enumset1(A_170, A_170, B_176, C_171, D_175, E_172, F_173, G_174)=k5_enumset1(A_170, B_176, C_171, D_175, E_172, F_173, G_174))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.02/1.39  tff(c_22, plain, (![G_35, H_36, E_33, J_40, A_29, D_32, C_31, B_30]: (r2_hidden(J_40, k6_enumset1(A_29, B_30, C_31, D_32, E_33, J_40, G_35, H_36)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.02/1.39  tff(c_286, plain, (![B_180, D_183, E_178, C_181, A_177, G_182, F_179]: (r2_hidden(E_178, k5_enumset1(A_177, B_180, C_181, D_183, E_178, F_179, G_182)))), inference(superposition, [status(thm), theory('equality')], [c_253, c_22])).
% 3.02/1.39  tff(c_290, plain, (![D_188, F_184, B_185, A_187, E_186, C_189]: (r2_hidden(D_188, k4_enumset1(A_187, B_185, C_189, D_188, E_186, F_184)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_286])).
% 3.02/1.39  tff(c_343, plain, (![A_200, C_199, E_203, D_202, B_201]: (r2_hidden(C_199, k3_enumset1(A_200, B_201, C_199, D_202, E_203)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_290])).
% 3.02/1.39  tff(c_347, plain, (![B_204, A_205, C_206, D_207]: (r2_hidden(B_204, k2_enumset1(A_205, B_204, C_206, D_207)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_343])).
% 3.02/1.39  tff(c_351, plain, (![A_208, B_209, C_210]: (r2_hidden(A_208, k1_enumset1(A_208, B_209, C_210)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_347])).
% 3.02/1.39  tff(c_356, plain, (![A_220, B_221]: (r2_hidden(A_220, k2_tarski(A_220, B_221)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_351])).
% 3.02/1.39  tff(c_360, plain, (![A_222]: (r2_hidden(A_222, k1_tarski(A_222)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_356])).
% 3.02/1.39  tff(c_363, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_205, c_360])).
% 3.02/1.39  tff(c_365, plain, $false, inference(negUnitSimplification, [status(thm)], [c_197, c_363])).
% 3.02/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.39  
% 3.02/1.39  Inference rules
% 3.02/1.39  ----------------------
% 3.02/1.39  #Ref     : 0
% 3.02/1.39  #Sup     : 57
% 3.02/1.39  #Fact    : 0
% 3.02/1.39  #Define  : 0
% 3.02/1.39  #Split   : 0
% 3.02/1.39  #Chain   : 0
% 3.02/1.39  #Close   : 0
% 3.02/1.39  
% 3.02/1.39  Ordering : KBO
% 3.02/1.39  
% 3.02/1.39  Simplification rules
% 3.02/1.39  ----------------------
% 3.02/1.39  #Subsume      : 0
% 3.02/1.39  #Demod        : 16
% 3.02/1.39  #Tautology    : 34
% 3.02/1.39  #SimpNegUnit  : 4
% 3.02/1.39  #BackRed      : 4
% 3.02/1.39  
% 3.02/1.39  #Partial instantiations: 0
% 3.02/1.39  #Strategies tried      : 1
% 3.02/1.39  
% 3.02/1.39  Timing (in seconds)
% 3.02/1.39  ----------------------
% 3.02/1.39  Preprocessing        : 0.36
% 3.02/1.39  Parsing              : 0.17
% 3.02/1.39  CNF conversion       : 0.03
% 3.02/1.39  Main loop            : 0.27
% 3.02/1.39  Inferencing          : 0.08
% 3.02/1.39  Reduction            : 0.08
% 3.02/1.39  Demodulation         : 0.05
% 3.02/1.39  BG Simplification    : 0.02
% 3.02/1.39  Subsumption          : 0.09
% 3.02/1.39  Abstraction          : 0.02
% 3.02/1.39  MUC search           : 0.00
% 3.02/1.39  Cooper               : 0.00
% 3.02/1.39  Total                : 0.67
% 3.02/1.39  Index Insertion      : 0.00
% 3.02/1.39  Index Deletion       : 0.00
% 3.02/1.39  Index Matching       : 0.00
% 3.02/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
