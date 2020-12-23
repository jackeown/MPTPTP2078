%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:13 EST 2020

% Result     : Theorem 7.25s
% Output     : CNFRefutation 7.45s
% Verified   : 
% Statistics : Number of formulae       :  170 (2578 expanded)
%              Number of leaves         :   51 ( 929 expanded)
%              Depth                    :   23
%              Number of atoms          :  337 (7975 expanded)
%              Number of equality atoms :   98 (2423 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_192,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( ( k2_relset_1(A,B,C) = B
                & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
                & v2_funct_1(C) )
             => ( A = k1_xboole_0
                | B = k1_xboole_0
                | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_128,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_166,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_78,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_154,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_142,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_140,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_164,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_132,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_112,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_94,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_122,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_66,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_78,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_140,plain,(
    ! [B_68,A_69] :
      ( v1_relat_1(B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_69))
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_149,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_78,c_140])).

tff(c_158,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_149])).

tff(c_264,plain,(
    ! [C_84,A_85,B_86] :
      ( v4_relat_1(C_84,A_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_277,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_264])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_84,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_146,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_84,c_140])).

tff(c_155,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_146])).

tff(c_276,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_264])).

tff(c_64,plain,(
    ! [A_55] : k6_relat_1(A_55) = k6_partfun1(A_55) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_24,plain,(
    ! [A_24] : k1_relat_1(k6_relat_1(A_24)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_95,plain,(
    ! [A_24] : k1_relat_1(k6_partfun1(A_24)) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_24])).

tff(c_88,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_82,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_2213,plain,(
    ! [E_188,D_184,F_185,A_186,C_183,B_187] :
      ( m1_subset_1(k1_partfun1(A_186,B_187,C_183,D_184,E_188,F_185),k1_zfmisc_1(k2_zfmisc_1(A_186,D_184)))
      | ~ m1_subset_1(F_185,k1_zfmisc_1(k2_zfmisc_1(C_183,D_184)))
      | ~ v1_funct_1(F_185)
      | ~ m1_subset_1(E_188,k1_zfmisc_1(k2_zfmisc_1(A_186,B_187)))
      | ~ v1_funct_1(E_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_56,plain,(
    ! [A_42] : m1_subset_1(k6_relat_1(A_42),k1_zfmisc_1(k2_zfmisc_1(A_42,A_42))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_89,plain,(
    ! [A_42] : m1_subset_1(k6_partfun1(A_42),k1_zfmisc_1(k2_zfmisc_1(A_42,A_42))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_56])).

tff(c_74,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_1697,plain,(
    ! [D_152,C_153,A_154,B_155] :
      ( D_152 = C_153
      | ~ r2_relset_1(A_154,B_155,C_153,D_152)
      | ~ m1_subset_1(D_152,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155)))
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1705,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_74,c_1697])).

tff(c_1720,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_1705])).

tff(c_1777,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1720])).

tff(c_2224,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2213,c_1777])).

tff(c_2247,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_84,c_82,c_78,c_2224])).

tff(c_2248,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1720])).

tff(c_2584,plain,(
    ! [A_207,C_203,F_206,B_205,D_208,E_204] :
      ( k1_partfun1(A_207,B_205,C_203,D_208,E_204,F_206) = k5_relat_1(E_204,F_206)
      | ~ m1_subset_1(F_206,k1_zfmisc_1(k2_zfmisc_1(C_203,D_208)))
      | ~ v1_funct_1(F_206)
      | ~ m1_subset_1(E_204,k1_zfmisc_1(k2_zfmisc_1(A_207,B_205)))
      | ~ v1_funct_1(E_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_2590,plain,(
    ! [A_207,B_205,E_204] :
      ( k1_partfun1(A_207,B_205,'#skF_2','#skF_1',E_204,'#skF_4') = k5_relat_1(E_204,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_204,k1_zfmisc_1(k2_zfmisc_1(A_207,B_205)))
      | ~ v1_funct_1(E_204) ) ),
    inference(resolution,[status(thm)],[c_78,c_2584])).

tff(c_3376,plain,(
    ! [A_233,B_234,E_235] :
      ( k1_partfun1(A_233,B_234,'#skF_2','#skF_1',E_235,'#skF_4') = k5_relat_1(E_235,'#skF_4')
      | ~ m1_subset_1(E_235,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234)))
      | ~ v1_funct_1(E_235) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2590])).

tff(c_3388,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_3376])).

tff(c_3399,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2248,c_3388])).

tff(c_20,plain,(
    ! [A_14,B_16] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_14,B_16)),k1_relat_1(A_14))
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3424,plain,
    ( r1_tarski(k1_relat_1(k6_partfun1('#skF_1')),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3399,c_20])).

tff(c_3440,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_158,c_95,c_3424])).

tff(c_206,plain,(
    ! [B_75,A_76] :
      ( r1_tarski(k1_relat_1(B_75),A_76)
      | ~ v4_relat_1(B_75,A_76)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_212,plain,(
    ! [B_75,A_76] :
      ( k1_relat_1(B_75) = A_76
      | ~ r1_tarski(A_76,k1_relat_1(B_75))
      | ~ v4_relat_1(B_75,A_76)
      | ~ v1_relat_1(B_75) ) ),
    inference(resolution,[status(thm)],[c_206,c_2])).

tff(c_3444,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3440,c_212])).

tff(c_3449,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_276,c_3444])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_76,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_398,plain,(
    ! [A_103,B_104,C_105] :
      ( k2_relset_1(A_103,B_104,C_105) = k2_relat_1(C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_404,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_398])).

tff(c_411,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_404])).

tff(c_30,plain,(
    ! [A_26] :
      ( k5_relat_1(A_26,k6_relat_1(k2_relat_1(A_26))) = A_26
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_92,plain,(
    ! [A_26] :
      ( k5_relat_1(A_26,k6_partfun1(k2_relat_1(A_26))) = A_26
      | ~ v1_relat_1(A_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_30])).

tff(c_143,plain,(
    ! [A_42] :
      ( v1_relat_1(k6_partfun1(A_42))
      | ~ v1_relat_1(k2_zfmisc_1(A_42,A_42)) ) ),
    inference(resolution,[status(thm)],[c_89,c_140])).

tff(c_152,plain,(
    ! [A_42] : v1_relat_1(k6_partfun1(A_42)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_143])).

tff(c_440,plain,(
    ! [A_107,B_108] :
      ( k10_relat_1(A_107,k1_relat_1(B_108)) = k1_relat_1(k5_relat_1(A_107,B_108))
      | ~ v1_relat_1(B_108)
      | ~ v1_relat_1(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_452,plain,(
    ! [A_107,A_24] :
      ( k1_relat_1(k5_relat_1(A_107,k6_partfun1(A_24))) = k10_relat_1(A_107,A_24)
      | ~ v1_relat_1(k6_partfun1(A_24))
      | ~ v1_relat_1(A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_440])).

tff(c_461,plain,(
    ! [A_109,A_110] :
      ( k1_relat_1(k5_relat_1(A_109,k6_partfun1(A_110))) = k10_relat_1(A_109,A_110)
      | ~ v1_relat_1(A_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_452])).

tff(c_508,plain,(
    ! [A_26] :
      ( k10_relat_1(A_26,k2_relat_1(A_26)) = k1_relat_1(A_26)
      | ~ v1_relat_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_461])).

tff(c_782,plain,(
    ! [B_123,A_124] :
      ( k9_relat_1(B_123,k10_relat_1(B_123,A_124)) = A_124
      | ~ r1_tarski(A_124,k2_relat_1(B_123))
      | ~ v1_funct_1(B_123)
      | ~ v1_relat_1(B_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_787,plain,(
    ! [A_124] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_124)) = A_124
      | ~ r1_tarski(A_124,'#skF_2')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_411,c_782])).

tff(c_828,plain,(
    ! [A_127] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_127)) = A_127
      | ~ r1_tarski(A_127,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_88,c_787])).

tff(c_838,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_508,c_828])).

tff(c_849,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_155,c_6,c_411,c_411,c_838])).

tff(c_3456,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3449,c_849])).

tff(c_18,plain,(
    ! [A_11,B_13] :
      ( k10_relat_1(A_11,k1_relat_1(B_13)) = k1_relat_1(k5_relat_1(A_11,B_13))
      | ~ v1_relat_1(B_13)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_845,plain,(
    ! [B_13] :
      ( k9_relat_1('#skF_3',k1_relat_1(k5_relat_1('#skF_3',B_13))) = k1_relat_1(B_13)
      | ~ r1_tarski(k1_relat_1(B_13),'#skF_2')
      | ~ v1_relat_1(B_13)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_828])).

tff(c_853,plain,(
    ! [B_13] :
      ( k9_relat_1('#skF_3',k1_relat_1(k5_relat_1('#skF_3',B_13))) = k1_relat_1(B_13)
      | ~ r1_tarski(k1_relat_1(B_13),'#skF_2')
      | ~ v1_relat_1(B_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_845])).

tff(c_3421,plain,
    ( k9_relat_1('#skF_3',k1_relat_1(k6_partfun1('#skF_1'))) = k1_relat_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3399,c_853])).

tff(c_3438,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_95,c_3421])).

tff(c_4087,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3456,c_3438])).

tff(c_4088,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_4087])).

tff(c_4091,plain,
    ( ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_4088])).

tff(c_4095,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_277,c_4091])).

tff(c_4096,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4087])).

tff(c_28,plain,(
    ! [A_25] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_25)),A_25) = A_25
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_93,plain,(
    ! [A_25] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_25)),A_25) = A_25
      | ~ v1_relat_1(A_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_28])).

tff(c_4134,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4096,c_93])).

tff(c_4166,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_4134])).

tff(c_72,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_38,plain,(
    ! [A_30] :
      ( k2_relat_1(k2_funct_1(A_30)) = k1_relat_1(A_30)
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_34,plain,(
    ! [A_27] :
      ( v1_relat_1(k2_funct_1(A_27))
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_44,plain,(
    ! [A_31] :
      ( k5_relat_1(A_31,k2_funct_1(A_31)) = k6_relat_1(k1_relat_1(A_31))
      | ~ v2_funct_1(A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_90,plain,(
    ! [A_31] :
      ( k5_relat_1(A_31,k2_funct_1(A_31)) = k6_partfun1(k1_relat_1(A_31))
      | ~ v2_funct_1(A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_44])).

tff(c_1008,plain,(
    ! [B_136] :
      ( k9_relat_1('#skF_3',k1_relat_1(k5_relat_1('#skF_3',B_136))) = k1_relat_1(B_136)
      | ~ r1_tarski(k1_relat_1(B_136),'#skF_2')
      | ~ v1_relat_1(B_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_845])).

tff(c_1018,plain,
    ( k9_relat_1('#skF_3',k1_relat_1(k6_partfun1(k1_relat_1('#skF_3')))) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_1008])).

tff(c_1033,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2'
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_88,c_72,c_849,c_95,c_1018])).

tff(c_1095,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1033])).

tff(c_1098,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_1095])).

tff(c_1102,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_88,c_1098])).

tff(c_1104,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1033])).

tff(c_40,plain,(
    ! [A_30] :
      ( k1_relat_1(k2_funct_1(A_30)) = k2_relat_1(A_30)
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1103,plain,
    ( ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2')
    | k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1033])).

tff(c_1105,plain,(
    ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1103])).

tff(c_1178,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1105])).

tff(c_1184,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_88,c_72,c_6,c_411,c_1178])).

tff(c_1185,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1103])).

tff(c_1217,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1185,c_93])).

tff(c_1248,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1104,c_1217])).

tff(c_1321,plain,(
    ! [A_144,B_145,C_146] :
      ( k5_relat_1(k5_relat_1(A_144,B_145),C_146) = k5_relat_1(A_144,k5_relat_1(B_145,C_146))
      | ~ v1_relat_1(C_146)
      | ~ v1_relat_1(B_145)
      | ~ v1_relat_1(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1351,plain,(
    ! [C_146] :
      ( k5_relat_1(k6_partfun1('#skF_2'),k5_relat_1(k2_funct_1('#skF_3'),C_146)) = k5_relat_1(k2_funct_1('#skF_3'),C_146)
      | ~ v1_relat_1(C_146)
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k6_partfun1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1248,c_1321])).

tff(c_2355,plain,(
    ! [C_197] :
      ( k5_relat_1(k6_partfun1('#skF_2'),k5_relat_1(k2_funct_1('#skF_3'),C_197)) = k5_relat_1(k2_funct_1('#skF_3'),C_197)
      | ~ v1_relat_1(C_197) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_1104,c_1351])).

tff(c_2391,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))) = k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_2355])).

tff(c_2405,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1104,c_152,c_1248,c_2391])).

tff(c_2468,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k1_relat_1('#skF_3'))) = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2405])).

tff(c_2488,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k1_relat_1('#skF_3'))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_88,c_72,c_2468])).

tff(c_3454,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3449,c_2488])).

tff(c_26,plain,(
    ! [A_24] : k2_relat_1(k6_relat_1(A_24)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_94,plain,(
    ! [A_24] : k2_relat_1(k6_partfun1(A_24)) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_26])).

tff(c_183,plain,(
    ! [A_73] :
      ( k5_relat_1(A_73,k6_partfun1(k2_relat_1(A_73))) = A_73
      | ~ v1_relat_1(A_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_30])).

tff(c_192,plain,(
    ! [A_24] :
      ( k5_relat_1(k6_partfun1(A_24),k6_partfun1(A_24)) = k6_partfun1(A_24)
      | ~ v1_relat_1(k6_partfun1(A_24)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_183])).

tff(c_196,plain,(
    ! [A_24] : k5_relat_1(k6_partfun1(A_24),k6_partfun1(A_24)) = k6_partfun1(A_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_192])).

tff(c_42,plain,(
    ! [A_31] :
      ( k5_relat_1(k2_funct_1(A_31),A_31) = k6_relat_1(k2_relat_1(A_31))
      | ~ v2_funct_1(A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_91,plain,(
    ! [A_31] :
      ( k5_relat_1(k2_funct_1(A_31),A_31) = k6_partfun1(k2_relat_1(A_31))
      | ~ v2_funct_1(A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_42])).

tff(c_2387,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),k6_partfun1(k2_relat_1('#skF_3'))) = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_2355])).

tff(c_2403,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_88,c_72,c_155,c_196,c_411,c_2387])).

tff(c_22,plain,(
    ! [A_17,B_21,C_23] :
      ( k5_relat_1(k5_relat_1(A_17,B_21),C_23) = k5_relat_1(A_17,k5_relat_1(B_21,C_23))
      | ~ v1_relat_1(C_23)
      | ~ v1_relat_1(B_21)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2421,plain,(
    ! [C_23] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_23)) = k5_relat_1(k6_partfun1('#skF_2'),C_23)
      | ~ v1_relat_1(C_23)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2403,c_22])).

tff(c_2438,plain,(
    ! [C_23] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_23)) = k5_relat_1(k6_partfun1('#skF_2'),C_23)
      | ~ v1_relat_1(C_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1104,c_155,c_2421])).

tff(c_3415,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3399,c_2438])).

tff(c_3434,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_3415])).

tff(c_5106,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4166,c_3454,c_3434])).

tff(c_5107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_5106])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:38:02 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.25/2.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.25/2.69  
% 7.25/2.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.25/2.69  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.25/2.69  
% 7.25/2.69  %Foreground sorts:
% 7.25/2.69  
% 7.25/2.69  
% 7.25/2.69  %Background operators:
% 7.25/2.69  
% 7.25/2.69  
% 7.25/2.69  %Foreground operators:
% 7.25/2.69  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.25/2.69  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.25/2.69  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.25/2.69  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.25/2.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.25/2.69  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.25/2.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.25/2.69  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.25/2.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.25/2.69  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.25/2.69  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.25/2.69  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.25/2.69  tff('#skF_2', type, '#skF_2': $i).
% 7.25/2.69  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.25/2.69  tff('#skF_3', type, '#skF_3': $i).
% 7.25/2.69  tff('#skF_1', type, '#skF_1': $i).
% 7.25/2.69  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.25/2.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.25/2.69  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.25/2.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.25/2.69  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.25/2.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.25/2.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.25/2.69  tff('#skF_4', type, '#skF_4': $i).
% 7.25/2.69  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.25/2.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.25/2.69  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.25/2.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.25/2.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.25/2.69  
% 7.45/2.72  tff(f_192, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 7.45/2.72  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.45/2.72  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.45/2.72  tff(f_128, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.45/2.72  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 7.45/2.72  tff(f_166, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.45/2.72  tff(f_78, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 7.45/2.72  tff(f_154, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.45/2.72  tff(f_142, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 7.45/2.72  tff(f_140, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.45/2.72  tff(f_164, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.45/2.72  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 7.45/2.72  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.45/2.72  tff(f_132, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.45/2.72  tff(f_86, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 7.45/2.72  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 7.45/2.72  tff(f_102, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 7.45/2.72  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 7.45/2.72  tff(f_112, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 7.45/2.72  tff(f_94, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 7.45/2.72  tff(f_122, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 7.45/2.72  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 7.45/2.72  tff(c_66, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.45/2.72  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.45/2.72  tff(c_78, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.45/2.72  tff(c_140, plain, (![B_68, A_69]: (v1_relat_1(B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(A_69)) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.45/2.72  tff(c_149, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_78, c_140])).
% 7.45/2.72  tff(c_158, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_149])).
% 7.45/2.72  tff(c_264, plain, (![C_84, A_85, B_86]: (v4_relat_1(C_84, A_85) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.45/2.72  tff(c_277, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_78, c_264])).
% 7.45/2.72  tff(c_12, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.45/2.72  tff(c_84, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.45/2.72  tff(c_146, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_84, c_140])).
% 7.45/2.72  tff(c_155, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_146])).
% 7.45/2.72  tff(c_276, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_84, c_264])).
% 7.45/2.72  tff(c_64, plain, (![A_55]: (k6_relat_1(A_55)=k6_partfun1(A_55))), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.45/2.72  tff(c_24, plain, (![A_24]: (k1_relat_1(k6_relat_1(A_24))=A_24)), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.45/2.72  tff(c_95, plain, (![A_24]: (k1_relat_1(k6_partfun1(A_24))=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_24])).
% 7.45/2.72  tff(c_88, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.45/2.72  tff(c_82, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.45/2.72  tff(c_2213, plain, (![E_188, D_184, F_185, A_186, C_183, B_187]: (m1_subset_1(k1_partfun1(A_186, B_187, C_183, D_184, E_188, F_185), k1_zfmisc_1(k2_zfmisc_1(A_186, D_184))) | ~m1_subset_1(F_185, k1_zfmisc_1(k2_zfmisc_1(C_183, D_184))) | ~v1_funct_1(F_185) | ~m1_subset_1(E_188, k1_zfmisc_1(k2_zfmisc_1(A_186, B_187))) | ~v1_funct_1(E_188))), inference(cnfTransformation, [status(thm)], [f_154])).
% 7.45/2.72  tff(c_56, plain, (![A_42]: (m1_subset_1(k6_relat_1(A_42), k1_zfmisc_1(k2_zfmisc_1(A_42, A_42))))), inference(cnfTransformation, [status(thm)], [f_142])).
% 7.45/2.72  tff(c_89, plain, (![A_42]: (m1_subset_1(k6_partfun1(A_42), k1_zfmisc_1(k2_zfmisc_1(A_42, A_42))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_56])).
% 7.45/2.72  tff(c_74, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.45/2.72  tff(c_1697, plain, (![D_152, C_153, A_154, B_155]: (D_152=C_153 | ~r2_relset_1(A_154, B_155, C_153, D_152) | ~m1_subset_1(D_152, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 7.45/2.72  tff(c_1705, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_74, c_1697])).
% 7.45/2.72  tff(c_1720, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_1705])).
% 7.45/2.72  tff(c_1777, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1720])).
% 7.45/2.72  tff(c_2224, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2213, c_1777])).
% 7.45/2.72  tff(c_2247, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_84, c_82, c_78, c_2224])).
% 7.45/2.72  tff(c_2248, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1720])).
% 7.45/2.72  tff(c_2584, plain, (![A_207, C_203, F_206, B_205, D_208, E_204]: (k1_partfun1(A_207, B_205, C_203, D_208, E_204, F_206)=k5_relat_1(E_204, F_206) | ~m1_subset_1(F_206, k1_zfmisc_1(k2_zfmisc_1(C_203, D_208))) | ~v1_funct_1(F_206) | ~m1_subset_1(E_204, k1_zfmisc_1(k2_zfmisc_1(A_207, B_205))) | ~v1_funct_1(E_204))), inference(cnfTransformation, [status(thm)], [f_164])).
% 7.45/2.72  tff(c_2590, plain, (![A_207, B_205, E_204]: (k1_partfun1(A_207, B_205, '#skF_2', '#skF_1', E_204, '#skF_4')=k5_relat_1(E_204, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_204, k1_zfmisc_1(k2_zfmisc_1(A_207, B_205))) | ~v1_funct_1(E_204))), inference(resolution, [status(thm)], [c_78, c_2584])).
% 7.45/2.72  tff(c_3376, plain, (![A_233, B_234, E_235]: (k1_partfun1(A_233, B_234, '#skF_2', '#skF_1', E_235, '#skF_4')=k5_relat_1(E_235, '#skF_4') | ~m1_subset_1(E_235, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))) | ~v1_funct_1(E_235))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_2590])).
% 7.45/2.72  tff(c_3388, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_3376])).
% 7.45/2.72  tff(c_3399, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_2248, c_3388])).
% 7.45/2.72  tff(c_20, plain, (![A_14, B_16]: (r1_tarski(k1_relat_1(k5_relat_1(A_14, B_16)), k1_relat_1(A_14)) | ~v1_relat_1(B_16) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.45/2.72  tff(c_3424, plain, (r1_tarski(k1_relat_1(k6_partfun1('#skF_1')), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3399, c_20])).
% 7.45/2.72  tff(c_3440, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_158, c_95, c_3424])).
% 7.45/2.72  tff(c_206, plain, (![B_75, A_76]: (r1_tarski(k1_relat_1(B_75), A_76) | ~v4_relat_1(B_75, A_76) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.45/2.72  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.45/2.72  tff(c_212, plain, (![B_75, A_76]: (k1_relat_1(B_75)=A_76 | ~r1_tarski(A_76, k1_relat_1(B_75)) | ~v4_relat_1(B_75, A_76) | ~v1_relat_1(B_75))), inference(resolution, [status(thm)], [c_206, c_2])).
% 7.45/2.72  tff(c_3444, plain, (k1_relat_1('#skF_3')='#skF_1' | ~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3440, c_212])).
% 7.45/2.72  tff(c_3449, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_155, c_276, c_3444])).
% 7.45/2.72  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.45/2.72  tff(c_76, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.45/2.72  tff(c_398, plain, (![A_103, B_104, C_105]: (k2_relset_1(A_103, B_104, C_105)=k2_relat_1(C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.45/2.72  tff(c_404, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_398])).
% 7.45/2.72  tff(c_411, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_404])).
% 7.45/2.72  tff(c_30, plain, (![A_26]: (k5_relat_1(A_26, k6_relat_1(k2_relat_1(A_26)))=A_26 | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.45/2.72  tff(c_92, plain, (![A_26]: (k5_relat_1(A_26, k6_partfun1(k2_relat_1(A_26)))=A_26 | ~v1_relat_1(A_26))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_30])).
% 7.45/2.72  tff(c_143, plain, (![A_42]: (v1_relat_1(k6_partfun1(A_42)) | ~v1_relat_1(k2_zfmisc_1(A_42, A_42)))), inference(resolution, [status(thm)], [c_89, c_140])).
% 7.45/2.72  tff(c_152, plain, (![A_42]: (v1_relat_1(k6_partfun1(A_42)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_143])).
% 7.45/2.72  tff(c_440, plain, (![A_107, B_108]: (k10_relat_1(A_107, k1_relat_1(B_108))=k1_relat_1(k5_relat_1(A_107, B_108)) | ~v1_relat_1(B_108) | ~v1_relat_1(A_107))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.45/2.72  tff(c_452, plain, (![A_107, A_24]: (k1_relat_1(k5_relat_1(A_107, k6_partfun1(A_24)))=k10_relat_1(A_107, A_24) | ~v1_relat_1(k6_partfun1(A_24)) | ~v1_relat_1(A_107))), inference(superposition, [status(thm), theory('equality')], [c_95, c_440])).
% 7.45/2.72  tff(c_461, plain, (![A_109, A_110]: (k1_relat_1(k5_relat_1(A_109, k6_partfun1(A_110)))=k10_relat_1(A_109, A_110) | ~v1_relat_1(A_109))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_452])).
% 7.45/2.72  tff(c_508, plain, (![A_26]: (k10_relat_1(A_26, k2_relat_1(A_26))=k1_relat_1(A_26) | ~v1_relat_1(A_26) | ~v1_relat_1(A_26))), inference(superposition, [status(thm), theory('equality')], [c_92, c_461])).
% 7.45/2.72  tff(c_782, plain, (![B_123, A_124]: (k9_relat_1(B_123, k10_relat_1(B_123, A_124))=A_124 | ~r1_tarski(A_124, k2_relat_1(B_123)) | ~v1_funct_1(B_123) | ~v1_relat_1(B_123))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.45/2.72  tff(c_787, plain, (![A_124]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_124))=A_124 | ~r1_tarski(A_124, '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_411, c_782])).
% 7.45/2.72  tff(c_828, plain, (![A_127]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_127))=A_127 | ~r1_tarski(A_127, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_88, c_787])).
% 7.45/2.72  tff(c_838, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_508, c_828])).
% 7.45/2.72  tff(c_849, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_155, c_155, c_6, c_411, c_411, c_838])).
% 7.45/2.72  tff(c_3456, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3449, c_849])).
% 7.45/2.72  tff(c_18, plain, (![A_11, B_13]: (k10_relat_1(A_11, k1_relat_1(B_13))=k1_relat_1(k5_relat_1(A_11, B_13)) | ~v1_relat_1(B_13) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.45/2.72  tff(c_845, plain, (![B_13]: (k9_relat_1('#skF_3', k1_relat_1(k5_relat_1('#skF_3', B_13)))=k1_relat_1(B_13) | ~r1_tarski(k1_relat_1(B_13), '#skF_2') | ~v1_relat_1(B_13) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_828])).
% 7.45/2.72  tff(c_853, plain, (![B_13]: (k9_relat_1('#skF_3', k1_relat_1(k5_relat_1('#skF_3', B_13)))=k1_relat_1(B_13) | ~r1_tarski(k1_relat_1(B_13), '#skF_2') | ~v1_relat_1(B_13))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_845])).
% 7.45/2.72  tff(c_3421, plain, (k9_relat_1('#skF_3', k1_relat_1(k6_partfun1('#skF_1')))=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3399, c_853])).
% 7.45/2.72  tff(c_3438, plain, (k9_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_95, c_3421])).
% 7.45/2.72  tff(c_4087, plain, (k1_relat_1('#skF_4')='#skF_2' | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3456, c_3438])).
% 7.45/2.72  tff(c_4088, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(splitLeft, [status(thm)], [c_4087])).
% 7.45/2.72  tff(c_4091, plain, (~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_4088])).
% 7.45/2.72  tff(c_4095, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_158, c_277, c_4091])).
% 7.45/2.72  tff(c_4096, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_4087])).
% 7.45/2.72  tff(c_28, plain, (![A_25]: (k5_relat_1(k6_relat_1(k1_relat_1(A_25)), A_25)=A_25 | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.45/2.72  tff(c_93, plain, (![A_25]: (k5_relat_1(k6_partfun1(k1_relat_1(A_25)), A_25)=A_25 | ~v1_relat_1(A_25))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_28])).
% 7.45/2.72  tff(c_4134, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4096, c_93])).
% 7.45/2.72  tff(c_4166, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_158, c_4134])).
% 7.45/2.72  tff(c_72, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_192])).
% 7.45/2.72  tff(c_38, plain, (![A_30]: (k2_relat_1(k2_funct_1(A_30))=k1_relat_1(A_30) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.45/2.72  tff(c_34, plain, (![A_27]: (v1_relat_1(k2_funct_1(A_27)) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.45/2.72  tff(c_44, plain, (![A_31]: (k5_relat_1(A_31, k2_funct_1(A_31))=k6_relat_1(k1_relat_1(A_31)) | ~v2_funct_1(A_31) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.45/2.72  tff(c_90, plain, (![A_31]: (k5_relat_1(A_31, k2_funct_1(A_31))=k6_partfun1(k1_relat_1(A_31)) | ~v2_funct_1(A_31) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_44])).
% 7.45/2.72  tff(c_1008, plain, (![B_136]: (k9_relat_1('#skF_3', k1_relat_1(k5_relat_1('#skF_3', B_136)))=k1_relat_1(B_136) | ~r1_tarski(k1_relat_1(B_136), '#skF_2') | ~v1_relat_1(B_136))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_845])).
% 7.45/2.72  tff(c_1018, plain, (k9_relat_1('#skF_3', k1_relat_1(k6_partfun1(k1_relat_1('#skF_3'))))=k1_relat_1(k2_funct_1('#skF_3')) | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_90, c_1008])).
% 7.45/2.72  tff(c_1033, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2' | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_88, c_72, c_849, c_95, c_1018])).
% 7.45/2.72  tff(c_1095, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1033])).
% 7.45/2.72  tff(c_1098, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_1095])).
% 7.45/2.72  tff(c_1102, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_155, c_88, c_1098])).
% 7.45/2.72  tff(c_1104, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1033])).
% 7.45/2.72  tff(c_40, plain, (![A_30]: (k1_relat_1(k2_funct_1(A_30))=k2_relat_1(A_30) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.45/2.72  tff(c_1103, plain, (~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2') | k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_1033])).
% 7.45/2.72  tff(c_1105, plain, (~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2')), inference(splitLeft, [status(thm)], [c_1103])).
% 7.45/2.72  tff(c_1178, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_40, c_1105])).
% 7.45/2.72  tff(c_1184, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_155, c_88, c_72, c_6, c_411, c_1178])).
% 7.45/2.72  tff(c_1185, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_1103])).
% 7.45/2.72  tff(c_1217, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1185, c_93])).
% 7.45/2.72  tff(c_1248, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1104, c_1217])).
% 7.45/2.72  tff(c_1321, plain, (![A_144, B_145, C_146]: (k5_relat_1(k5_relat_1(A_144, B_145), C_146)=k5_relat_1(A_144, k5_relat_1(B_145, C_146)) | ~v1_relat_1(C_146) | ~v1_relat_1(B_145) | ~v1_relat_1(A_144))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.45/2.72  tff(c_1351, plain, (![C_146]: (k5_relat_1(k6_partfun1('#skF_2'), k5_relat_1(k2_funct_1('#skF_3'), C_146))=k5_relat_1(k2_funct_1('#skF_3'), C_146) | ~v1_relat_1(C_146) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k6_partfun1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1248, c_1321])).
% 7.45/2.72  tff(c_2355, plain, (![C_197]: (k5_relat_1(k6_partfun1('#skF_2'), k5_relat_1(k2_funct_1('#skF_3'), C_197))=k5_relat_1(k2_funct_1('#skF_3'), C_197) | ~v1_relat_1(C_197))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_1104, c_1351])).
% 7.45/2.72  tff(c_2391, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))))=k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3')) | ~v1_relat_1(k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_92, c_2355])).
% 7.45/2.72  tff(c_2405, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1104, c_152, c_1248, c_2391])).
% 7.45/2.72  tff(c_2468, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k1_relat_1('#skF_3')))=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_38, c_2405])).
% 7.45/2.72  tff(c_2488, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k1_relat_1('#skF_3')))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_88, c_72, c_2468])).
% 7.45/2.72  tff(c_3454, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3449, c_2488])).
% 7.45/2.72  tff(c_26, plain, (![A_24]: (k2_relat_1(k6_relat_1(A_24))=A_24)), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.45/2.72  tff(c_94, plain, (![A_24]: (k2_relat_1(k6_partfun1(A_24))=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_26])).
% 7.45/2.72  tff(c_183, plain, (![A_73]: (k5_relat_1(A_73, k6_partfun1(k2_relat_1(A_73)))=A_73 | ~v1_relat_1(A_73))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_30])).
% 7.45/2.72  tff(c_192, plain, (![A_24]: (k5_relat_1(k6_partfun1(A_24), k6_partfun1(A_24))=k6_partfun1(A_24) | ~v1_relat_1(k6_partfun1(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_94, c_183])).
% 7.45/2.72  tff(c_196, plain, (![A_24]: (k5_relat_1(k6_partfun1(A_24), k6_partfun1(A_24))=k6_partfun1(A_24))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_192])).
% 7.45/2.72  tff(c_42, plain, (![A_31]: (k5_relat_1(k2_funct_1(A_31), A_31)=k6_relat_1(k2_relat_1(A_31)) | ~v2_funct_1(A_31) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.45/2.72  tff(c_91, plain, (![A_31]: (k5_relat_1(k2_funct_1(A_31), A_31)=k6_partfun1(k2_relat_1(A_31)) | ~v2_funct_1(A_31) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_42])).
% 7.45/2.72  tff(c_2387, plain, (k5_relat_1(k6_partfun1('#skF_2'), k6_partfun1(k2_relat_1('#skF_3')))=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_91, c_2355])).
% 7.45/2.72  tff(c_2403, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_88, c_72, c_155, c_196, c_411, c_2387])).
% 7.45/2.72  tff(c_22, plain, (![A_17, B_21, C_23]: (k5_relat_1(k5_relat_1(A_17, B_21), C_23)=k5_relat_1(A_17, k5_relat_1(B_21, C_23)) | ~v1_relat_1(C_23) | ~v1_relat_1(B_21) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.45/2.72  tff(c_2421, plain, (![C_23]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_23))=k5_relat_1(k6_partfun1('#skF_2'), C_23) | ~v1_relat_1(C_23) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2403, c_22])).
% 7.45/2.72  tff(c_2438, plain, (![C_23]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_23))=k5_relat_1(k6_partfun1('#skF_2'), C_23) | ~v1_relat_1(C_23))), inference(demodulation, [status(thm), theory('equality')], [c_1104, c_155, c_2421])).
% 7.45/2.72  tff(c_3415, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3399, c_2438])).
% 7.45/2.72  tff(c_3434, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_3415])).
% 7.45/2.72  tff(c_5106, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4166, c_3454, c_3434])).
% 7.45/2.72  tff(c_5107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_5106])).
% 7.45/2.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.45/2.72  
% 7.45/2.72  Inference rules
% 7.45/2.72  ----------------------
% 7.45/2.72  #Ref     : 0
% 7.45/2.72  #Sup     : 1080
% 7.45/2.72  #Fact    : 0
% 7.45/2.72  #Define  : 0
% 7.45/2.72  #Split   : 6
% 7.45/2.72  #Chain   : 0
% 7.45/2.72  #Close   : 0
% 7.45/2.72  
% 7.45/2.72  Ordering : KBO
% 7.45/2.72  
% 7.45/2.72  Simplification rules
% 7.45/2.72  ----------------------
% 7.45/2.72  #Subsume      : 77
% 7.45/2.72  #Demod        : 1788
% 7.45/2.72  #Tautology    : 523
% 7.45/2.72  #SimpNegUnit  : 1
% 7.45/2.72  #BackRed      : 17
% 7.45/2.72  
% 7.45/2.72  #Partial instantiations: 0
% 7.45/2.72  #Strategies tried      : 1
% 7.45/2.72  
% 7.45/2.72  Timing (in seconds)
% 7.45/2.72  ----------------------
% 7.45/2.72  Preprocessing        : 0.58
% 7.45/2.72  Parsing              : 0.30
% 7.45/2.72  CNF conversion       : 0.05
% 7.45/2.72  Main loop            : 1.21
% 7.45/2.72  Inferencing          : 0.41
% 7.45/2.72  Reduction            : 0.47
% 7.45/2.72  Demodulation         : 0.36
% 7.45/2.72  BG Simplification    : 0.06
% 7.45/2.72  Subsumption          : 0.20
% 7.45/2.72  Abstraction          : 0.05
% 7.45/2.72  MUC search           : 0.00
% 7.45/2.72  Cooper               : 0.00
% 7.45/2.72  Total                : 1.85
% 7.45/2.72  Index Insertion      : 0.00
% 7.45/2.72  Index Deletion       : 0.00
% 7.45/2.72  Index Matching       : 0.00
% 7.45/2.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
