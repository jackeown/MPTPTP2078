%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:13 EST 2020

% Result     : Theorem 6.23s
% Output     : CNFRefutation 6.48s
% Verified   : 
% Statistics : Number of formulae       :  171 (2079 expanded)
%              Number of leaves         :   52 ( 745 expanded)
%              Depth                    :   23
%              Number of atoms          :  333 (6744 expanded)
%              Number of equality atoms :   98 (2007 expanded)
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

tff(f_189,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_125,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_163,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_75,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_151,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_139,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_137,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_161,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_129,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_109,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_91,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_119,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_66,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_78,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_140,plain,(
    ! [B_67,A_68] :
      ( v1_relat_1(B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_68))
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_149,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_78,c_140])).

tff(c_158,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_149])).

tff(c_291,plain,(
    ! [C_89,A_90,B_91] :
      ( v4_relat_1(C_89,A_90)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_303,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_291])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_84,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_146,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_84,c_140])).

tff(c_155,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_146])).

tff(c_302,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_291])).

tff(c_64,plain,(
    ! [A_54] : k6_relat_1(A_54) = k6_partfun1(A_54) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_24,plain,(
    ! [A_23] : k1_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_95,plain,(
    ! [A_23] : k1_relat_1(k6_partfun1(A_23)) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_24])).

tff(c_88,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_82,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_2068,plain,(
    ! [C_187,A_185,D_183,B_184,E_182,F_186] :
      ( m1_subset_1(k1_partfun1(A_185,B_184,C_187,D_183,E_182,F_186),k1_zfmisc_1(k2_zfmisc_1(A_185,D_183)))
      | ~ m1_subset_1(F_186,k1_zfmisc_1(k2_zfmisc_1(C_187,D_183)))
      | ~ v1_funct_1(F_186)
      | ~ m1_subset_1(E_182,k1_zfmisc_1(k2_zfmisc_1(A_185,B_184)))
      | ~ v1_funct_1(E_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_56,plain,(
    ! [A_41] : m1_subset_1(k6_relat_1(A_41),k1_zfmisc_1(k2_zfmisc_1(A_41,A_41))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_89,plain,(
    ! [A_41] : m1_subset_1(k6_partfun1(A_41),k1_zfmisc_1(k2_zfmisc_1(A_41,A_41))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_56])).

tff(c_74,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_1494,plain,(
    ! [D_146,C_147,A_148,B_149] :
      ( D_146 = C_147
      | ~ r2_relset_1(A_148,B_149,C_147,D_146)
      | ~ m1_subset_1(D_146,k1_zfmisc_1(k2_zfmisc_1(A_148,B_149)))
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_148,B_149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1502,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_74,c_1494])).

tff(c_1517,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_1502])).

tff(c_1562,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1517])).

tff(c_2081,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2068,c_1562])).

tff(c_2103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_84,c_82,c_78,c_2081])).

tff(c_2104,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1517])).

tff(c_2503,plain,(
    ! [C_211,B_209,E_212,D_208,A_210,F_207] :
      ( k1_partfun1(A_210,B_209,C_211,D_208,E_212,F_207) = k5_relat_1(E_212,F_207)
      | ~ m1_subset_1(F_207,k1_zfmisc_1(k2_zfmisc_1(C_211,D_208)))
      | ~ v1_funct_1(F_207)
      | ~ m1_subset_1(E_212,k1_zfmisc_1(k2_zfmisc_1(A_210,B_209)))
      | ~ v1_funct_1(E_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_2509,plain,(
    ! [A_210,B_209,E_212] :
      ( k1_partfun1(A_210,B_209,'#skF_2','#skF_1',E_212,'#skF_4') = k5_relat_1(E_212,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_212,k1_zfmisc_1(k2_zfmisc_1(A_210,B_209)))
      | ~ v1_funct_1(E_212) ) ),
    inference(resolution,[status(thm)],[c_78,c_2503])).

tff(c_3105,plain,(
    ! [A_233,B_234,E_235] :
      ( k1_partfun1(A_233,B_234,'#skF_2','#skF_1',E_235,'#skF_4') = k5_relat_1(E_235,'#skF_4')
      | ~ m1_subset_1(E_235,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234)))
      | ~ v1_funct_1(E_235) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2509])).

tff(c_3117,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_3105])).

tff(c_3128,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2104,c_3117])).

tff(c_433,plain,(
    ! [A_107,B_108] :
      ( k10_relat_1(A_107,k1_relat_1(B_108)) = k1_relat_1(k5_relat_1(A_107,B_108))
      | ~ v1_relat_1(B_108)
      | ~ v1_relat_1(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k10_relat_1(B_11,A_10),k1_relat_1(B_11))
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_451,plain,(
    ! [A_107,B_108] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_107,B_108)),k1_relat_1(A_107))
      | ~ v1_relat_1(A_107)
      | ~ v1_relat_1(B_108)
      | ~ v1_relat_1(A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_433,c_16])).

tff(c_3141,plain,
    ( r1_tarski(k1_relat_1(k6_partfun1('#skF_1')),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3128,c_451])).

tff(c_3155,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_158,c_155,c_95,c_3141])).

tff(c_265,plain,(
    ! [B_82,A_83] :
      ( r1_tarski(k1_relat_1(B_82),A_83)
      | ~ v4_relat_1(B_82,A_83)
      | ~ v1_relat_1(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_271,plain,(
    ! [B_82,A_83] :
      ( k1_relat_1(B_82) = A_83
      | ~ r1_tarski(A_83,k1_relat_1(B_82))
      | ~ v4_relat_1(B_82,A_83)
      | ~ v1_relat_1(B_82) ) ),
    inference(resolution,[status(thm)],[c_265,c_2])).

tff(c_3163,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3155,c_271])).

tff(c_3168,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_302,c_3163])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_76,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_395,plain,(
    ! [A_104,B_105,C_106] :
      ( k2_relset_1(A_104,B_105,C_106) = k2_relat_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_401,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_395])).

tff(c_408,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_401])).

tff(c_18,plain,(
    ! [A_12] :
      ( k10_relat_1(A_12,k2_relat_1(A_12)) = k1_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_413,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_18])).

tff(c_420,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_413])).

tff(c_494,plain,(
    ! [B_110,A_111] :
      ( k9_relat_1(B_110,k10_relat_1(B_110,A_111)) = A_111
      | ~ r1_tarski(A_111,k2_relat_1(B_110))
      | ~ v1_funct_1(B_110)
      | ~ v1_relat_1(B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_496,plain,(
    ! [A_111] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_111)) = A_111
      | ~ r1_tarski(A_111,'#skF_2')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_494])).

tff(c_544,plain,(
    ! [A_114] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_114)) = A_114
      | ~ r1_tarski(A_114,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_88,c_496])).

tff(c_557,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_544])).

tff(c_567,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_557])).

tff(c_3173,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3168,c_567])).

tff(c_20,plain,(
    ! [A_13,B_15] :
      ( k10_relat_1(A_13,k1_relat_1(B_15)) = k1_relat_1(k5_relat_1(A_13,B_15))
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_554,plain,(
    ! [B_15] :
      ( k9_relat_1('#skF_3',k1_relat_1(k5_relat_1('#skF_3',B_15))) = k1_relat_1(B_15)
      | ~ r1_tarski(k1_relat_1(B_15),'#skF_2')
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_544])).

tff(c_565,plain,(
    ! [B_15] :
      ( k9_relat_1('#skF_3',k1_relat_1(k5_relat_1('#skF_3',B_15))) = k1_relat_1(B_15)
      | ~ r1_tarski(k1_relat_1(B_15),'#skF_2')
      | ~ v1_relat_1(B_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_554])).

tff(c_3147,plain,
    ( k9_relat_1('#skF_3',k1_relat_1(k6_partfun1('#skF_1'))) = k1_relat_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3128,c_565])).

tff(c_3159,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_95,c_3147])).

tff(c_3853,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3173,c_3159])).

tff(c_3854,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3853])).

tff(c_3857,plain,
    ( ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_3854])).

tff(c_3861,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_303,c_3857])).

tff(c_3862,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3853])).

tff(c_28,plain,(
    ! [A_24] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_24)),A_24) = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_93,plain,(
    ! [A_24] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_24)),A_24) = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_28])).

tff(c_3897,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3862,c_93])).

tff(c_3924,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_3897])).

tff(c_72,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_38,plain,(
    ! [A_29] :
      ( k2_relat_1(k2_funct_1(A_29)) = k1_relat_1(A_29)
      | ~ v2_funct_1(A_29)
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_34,plain,(
    ! [A_26] :
      ( v1_relat_1(k2_funct_1(A_26))
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_44,plain,(
    ! [A_30] :
      ( k5_relat_1(A_30,k2_funct_1(A_30)) = k6_relat_1(k1_relat_1(A_30))
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_90,plain,(
    ! [A_30] :
      ( k5_relat_1(A_30,k2_funct_1(A_30)) = k6_partfun1(k1_relat_1(A_30))
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_44])).

tff(c_746,plain,(
    ! [B_121] :
      ( k9_relat_1('#skF_3',k1_relat_1(k5_relat_1('#skF_3',B_121))) = k1_relat_1(B_121)
      | ~ r1_tarski(k1_relat_1(B_121),'#skF_2')
      | ~ v1_relat_1(B_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_554])).

tff(c_756,plain,
    ( k9_relat_1('#skF_3',k1_relat_1(k6_partfun1(k1_relat_1('#skF_3')))) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_746])).

tff(c_771,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2'
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_88,c_72,c_567,c_95,c_756])).

tff(c_907,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_771])).

tff(c_910,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_907])).

tff(c_914,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_88,c_910])).

tff(c_916,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_771])).

tff(c_143,plain,(
    ! [A_41] :
      ( v1_relat_1(k6_partfun1(A_41))
      | ~ v1_relat_1(k2_zfmisc_1(A_41,A_41)) ) ),
    inference(resolution,[status(thm)],[c_89,c_140])).

tff(c_152,plain,(
    ! [A_41] : v1_relat_1(k6_partfun1(A_41)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_143])).

tff(c_40,plain,(
    ! [A_29] :
      ( k1_relat_1(k2_funct_1(A_29)) = k2_relat_1(A_29)
      | ~ v2_funct_1(A_29)
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_915,plain,
    ( ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2')
    | k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_771])).

tff(c_917,plain,(
    ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_915])).

tff(c_920,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_917])).

tff(c_926,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_88,c_72,c_6,c_408,c_920])).

tff(c_927,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_915])).

tff(c_956,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_927,c_93])).

tff(c_982,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_916,c_956])).

tff(c_30,plain,(
    ! [A_25] :
      ( k5_relat_1(A_25,k6_relat_1(k2_relat_1(A_25))) = A_25
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_92,plain,(
    ! [A_25] :
      ( k5_relat_1(A_25,k6_partfun1(k2_relat_1(A_25))) = A_25
      | ~ v1_relat_1(A_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_30])).

tff(c_22,plain,(
    ! [A_16,B_20,C_22] :
      ( k5_relat_1(k5_relat_1(A_16,B_20),C_22) = k5_relat_1(A_16,k5_relat_1(B_20,C_22))
      | ~ v1_relat_1(C_22)
      | ~ v1_relat_1(B_20)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1100,plain,(
    ! [C_22] :
      ( k5_relat_1(k6_partfun1('#skF_2'),k5_relat_1(k2_funct_1('#skF_3'),C_22)) = k5_relat_1(k2_funct_1('#skF_3'),C_22)
      | ~ v1_relat_1(C_22)
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k6_partfun1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_982,c_22])).

tff(c_2546,plain,(
    ! [C_215] :
      ( k5_relat_1(k6_partfun1('#skF_2'),k5_relat_1(k2_funct_1('#skF_3'),C_215)) = k5_relat_1(k2_funct_1('#skF_3'),C_215)
      | ~ v1_relat_1(C_215) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_916,c_1100])).

tff(c_2585,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))) = k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_2546])).

tff(c_2599,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_916,c_152,c_982,c_2585])).

tff(c_2689,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k1_relat_1('#skF_3'))) = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2599])).

tff(c_2709,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(k1_relat_1('#skF_3'))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_88,c_72,c_2689])).

tff(c_3171,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3168,c_2709])).

tff(c_26,plain,(
    ! [A_23] : k2_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_94,plain,(
    ! [A_23] : k2_relat_1(k6_partfun1(A_23)) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_26])).

tff(c_173,plain,(
    ! [A_74] :
      ( k5_relat_1(A_74,k6_partfun1(k2_relat_1(A_74))) = A_74
      | ~ v1_relat_1(A_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_30])).

tff(c_182,plain,(
    ! [A_23] :
      ( k5_relat_1(k6_partfun1(A_23),k6_partfun1(A_23)) = k6_partfun1(A_23)
      | ~ v1_relat_1(k6_partfun1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_173])).

tff(c_186,plain,(
    ! [A_23] : k5_relat_1(k6_partfun1(A_23),k6_partfun1(A_23)) = k6_partfun1(A_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_182])).

tff(c_42,plain,(
    ! [A_30] :
      ( k5_relat_1(k2_funct_1(A_30),A_30) = k6_relat_1(k2_relat_1(A_30))
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_91,plain,(
    ! [A_30] :
      ( k5_relat_1(k2_funct_1(A_30),A_30) = k6_partfun1(k2_relat_1(A_30))
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_42])).

tff(c_2577,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),k6_partfun1(k2_relat_1('#skF_3'))) = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_2546])).

tff(c_2595,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_88,c_72,c_155,c_186,c_408,c_2577])).

tff(c_2621,plain,(
    ! [C_22] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_22)) = k5_relat_1(k6_partfun1('#skF_2'),C_22)
      | ~ v1_relat_1(C_22)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2595,c_22])).

tff(c_2637,plain,(
    ! [C_22] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_22)) = k5_relat_1(k6_partfun1('#skF_2'),C_22)
      | ~ v1_relat_1(C_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_916,c_155,c_2621])).

tff(c_3135,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3128,c_2637])).

tff(c_3151,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_3135])).

tff(c_4751,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3924,c_3171,c_3151])).

tff(c_4752,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_4751])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:40:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.23/2.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.23/2.26  
% 6.23/2.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.23/2.27  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.23/2.27  
% 6.23/2.27  %Foreground sorts:
% 6.23/2.27  
% 6.23/2.27  
% 6.23/2.27  %Background operators:
% 6.23/2.27  
% 6.23/2.27  
% 6.23/2.27  %Foreground operators:
% 6.23/2.27  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.23/2.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.23/2.27  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.23/2.27  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.23/2.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.23/2.27  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.23/2.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.23/2.27  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.23/2.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.23/2.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.23/2.27  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.23/2.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.23/2.27  tff('#skF_2', type, '#skF_2': $i).
% 6.23/2.27  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.23/2.27  tff('#skF_3', type, '#skF_3': $i).
% 6.23/2.27  tff('#skF_1', type, '#skF_1': $i).
% 6.23/2.27  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.23/2.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.23/2.27  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.23/2.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.23/2.27  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.23/2.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.23/2.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.23/2.27  tff('#skF_4', type, '#skF_4': $i).
% 6.23/2.27  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.23/2.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.23/2.27  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.23/2.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.23/2.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.23/2.27  
% 6.48/2.29  tff(f_189, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 6.48/2.29  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.48/2.29  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.48/2.29  tff(f_125, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.48/2.29  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 6.48/2.29  tff(f_163, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.48/2.29  tff(f_75, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 6.48/2.29  tff(f_151, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.48/2.29  tff(f_139, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 6.48/2.29  tff(f_137, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.48/2.29  tff(f_161, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.48/2.29  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 6.48/2.29  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 6.48/2.29  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.48/2.29  tff(f_129, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.48/2.29  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 6.48/2.29  tff(f_99, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 6.48/2.29  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 6.48/2.29  tff(f_109, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 6.48/2.29  tff(f_91, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 6.48/2.29  tff(f_119, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 6.48/2.29  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 6.48/2.29  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 6.48/2.29  tff(c_66, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_189])).
% 6.48/2.29  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.48/2.29  tff(c_78, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_189])).
% 6.48/2.29  tff(c_140, plain, (![B_67, A_68]: (v1_relat_1(B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(A_68)) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.48/2.29  tff(c_149, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_78, c_140])).
% 6.48/2.29  tff(c_158, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_149])).
% 6.48/2.29  tff(c_291, plain, (![C_89, A_90, B_91]: (v4_relat_1(C_89, A_90) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.48/2.29  tff(c_303, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_78, c_291])).
% 6.48/2.29  tff(c_12, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.48/2.29  tff(c_84, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_189])).
% 6.48/2.29  tff(c_146, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_84, c_140])).
% 6.48/2.29  tff(c_155, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_146])).
% 6.48/2.29  tff(c_302, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_84, c_291])).
% 6.48/2.29  tff(c_64, plain, (![A_54]: (k6_relat_1(A_54)=k6_partfun1(A_54))), inference(cnfTransformation, [status(thm)], [f_163])).
% 6.48/2.29  tff(c_24, plain, (![A_23]: (k1_relat_1(k6_relat_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.48/2.29  tff(c_95, plain, (![A_23]: (k1_relat_1(k6_partfun1(A_23))=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_24])).
% 6.48/2.29  tff(c_88, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_189])).
% 6.48/2.29  tff(c_82, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_189])).
% 6.48/2.29  tff(c_2068, plain, (![C_187, A_185, D_183, B_184, E_182, F_186]: (m1_subset_1(k1_partfun1(A_185, B_184, C_187, D_183, E_182, F_186), k1_zfmisc_1(k2_zfmisc_1(A_185, D_183))) | ~m1_subset_1(F_186, k1_zfmisc_1(k2_zfmisc_1(C_187, D_183))) | ~v1_funct_1(F_186) | ~m1_subset_1(E_182, k1_zfmisc_1(k2_zfmisc_1(A_185, B_184))) | ~v1_funct_1(E_182))), inference(cnfTransformation, [status(thm)], [f_151])).
% 6.48/2.29  tff(c_56, plain, (![A_41]: (m1_subset_1(k6_relat_1(A_41), k1_zfmisc_1(k2_zfmisc_1(A_41, A_41))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.48/2.29  tff(c_89, plain, (![A_41]: (m1_subset_1(k6_partfun1(A_41), k1_zfmisc_1(k2_zfmisc_1(A_41, A_41))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_56])).
% 6.48/2.29  tff(c_74, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_189])).
% 6.48/2.29  tff(c_1494, plain, (![D_146, C_147, A_148, B_149]: (D_146=C_147 | ~r2_relset_1(A_148, B_149, C_147, D_146) | ~m1_subset_1(D_146, k1_zfmisc_1(k2_zfmisc_1(A_148, B_149))) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_148, B_149))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.48/2.29  tff(c_1502, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_74, c_1494])).
% 6.48/2.29  tff(c_1517, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_1502])).
% 6.48/2.29  tff(c_1562, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1517])).
% 6.48/2.29  tff(c_2081, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2068, c_1562])).
% 6.48/2.29  tff(c_2103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_84, c_82, c_78, c_2081])).
% 6.48/2.29  tff(c_2104, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1517])).
% 6.48/2.29  tff(c_2503, plain, (![C_211, B_209, E_212, D_208, A_210, F_207]: (k1_partfun1(A_210, B_209, C_211, D_208, E_212, F_207)=k5_relat_1(E_212, F_207) | ~m1_subset_1(F_207, k1_zfmisc_1(k2_zfmisc_1(C_211, D_208))) | ~v1_funct_1(F_207) | ~m1_subset_1(E_212, k1_zfmisc_1(k2_zfmisc_1(A_210, B_209))) | ~v1_funct_1(E_212))), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.48/2.29  tff(c_2509, plain, (![A_210, B_209, E_212]: (k1_partfun1(A_210, B_209, '#skF_2', '#skF_1', E_212, '#skF_4')=k5_relat_1(E_212, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_212, k1_zfmisc_1(k2_zfmisc_1(A_210, B_209))) | ~v1_funct_1(E_212))), inference(resolution, [status(thm)], [c_78, c_2503])).
% 6.48/2.29  tff(c_3105, plain, (![A_233, B_234, E_235]: (k1_partfun1(A_233, B_234, '#skF_2', '#skF_1', E_235, '#skF_4')=k5_relat_1(E_235, '#skF_4') | ~m1_subset_1(E_235, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))) | ~v1_funct_1(E_235))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_2509])).
% 6.48/2.29  tff(c_3117, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_3105])).
% 6.48/2.29  tff(c_3128, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_2104, c_3117])).
% 6.48/2.29  tff(c_433, plain, (![A_107, B_108]: (k10_relat_1(A_107, k1_relat_1(B_108))=k1_relat_1(k5_relat_1(A_107, B_108)) | ~v1_relat_1(B_108) | ~v1_relat_1(A_107))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.48/2.29  tff(c_16, plain, (![B_11, A_10]: (r1_tarski(k10_relat_1(B_11, A_10), k1_relat_1(B_11)) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.48/2.29  tff(c_451, plain, (![A_107, B_108]: (r1_tarski(k1_relat_1(k5_relat_1(A_107, B_108)), k1_relat_1(A_107)) | ~v1_relat_1(A_107) | ~v1_relat_1(B_108) | ~v1_relat_1(A_107))), inference(superposition, [status(thm), theory('equality')], [c_433, c_16])).
% 6.48/2.29  tff(c_3141, plain, (r1_tarski(k1_relat_1(k6_partfun1('#skF_1')), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3128, c_451])).
% 6.48/2.29  tff(c_3155, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_158, c_155, c_95, c_3141])).
% 6.48/2.29  tff(c_265, plain, (![B_82, A_83]: (r1_tarski(k1_relat_1(B_82), A_83) | ~v4_relat_1(B_82, A_83) | ~v1_relat_1(B_82))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.48/2.29  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.48/2.29  tff(c_271, plain, (![B_82, A_83]: (k1_relat_1(B_82)=A_83 | ~r1_tarski(A_83, k1_relat_1(B_82)) | ~v4_relat_1(B_82, A_83) | ~v1_relat_1(B_82))), inference(resolution, [status(thm)], [c_265, c_2])).
% 6.48/2.29  tff(c_3163, plain, (k1_relat_1('#skF_3')='#skF_1' | ~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3155, c_271])).
% 6.48/2.29  tff(c_3168, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_155, c_302, c_3163])).
% 6.48/2.29  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.48/2.29  tff(c_76, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_189])).
% 6.48/2.29  tff(c_395, plain, (![A_104, B_105, C_106]: (k2_relset_1(A_104, B_105, C_106)=k2_relat_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.48/2.29  tff(c_401, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_395])).
% 6.48/2.29  tff(c_408, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_401])).
% 6.48/2.29  tff(c_18, plain, (![A_12]: (k10_relat_1(A_12, k2_relat_1(A_12))=k1_relat_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.48/2.29  tff(c_413, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_408, c_18])).
% 6.48/2.29  tff(c_420, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_413])).
% 6.48/2.29  tff(c_494, plain, (![B_110, A_111]: (k9_relat_1(B_110, k10_relat_1(B_110, A_111))=A_111 | ~r1_tarski(A_111, k2_relat_1(B_110)) | ~v1_funct_1(B_110) | ~v1_relat_1(B_110))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.48/2.29  tff(c_496, plain, (![A_111]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_111))=A_111 | ~r1_tarski(A_111, '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_408, c_494])).
% 6.48/2.29  tff(c_544, plain, (![A_114]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_114))=A_114 | ~r1_tarski(A_114, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_88, c_496])).
% 6.48/2.29  tff(c_557, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_2' | ~r1_tarski('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_420, c_544])).
% 6.48/2.29  tff(c_567, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_557])).
% 6.48/2.29  tff(c_3173, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3168, c_567])).
% 6.48/2.29  tff(c_20, plain, (![A_13, B_15]: (k10_relat_1(A_13, k1_relat_1(B_15))=k1_relat_1(k5_relat_1(A_13, B_15)) | ~v1_relat_1(B_15) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.48/2.29  tff(c_554, plain, (![B_15]: (k9_relat_1('#skF_3', k1_relat_1(k5_relat_1('#skF_3', B_15)))=k1_relat_1(B_15) | ~r1_tarski(k1_relat_1(B_15), '#skF_2') | ~v1_relat_1(B_15) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_20, c_544])).
% 6.48/2.29  tff(c_565, plain, (![B_15]: (k9_relat_1('#skF_3', k1_relat_1(k5_relat_1('#skF_3', B_15)))=k1_relat_1(B_15) | ~r1_tarski(k1_relat_1(B_15), '#skF_2') | ~v1_relat_1(B_15))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_554])).
% 6.48/2.29  tff(c_3147, plain, (k9_relat_1('#skF_3', k1_relat_1(k6_partfun1('#skF_1')))=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3128, c_565])).
% 6.48/2.29  tff(c_3159, plain, (k9_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_95, c_3147])).
% 6.48/2.29  tff(c_3853, plain, (k1_relat_1('#skF_4')='#skF_2' | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3173, c_3159])).
% 6.48/2.29  tff(c_3854, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(splitLeft, [status(thm)], [c_3853])).
% 6.48/2.29  tff(c_3857, plain, (~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_3854])).
% 6.48/2.29  tff(c_3861, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_158, c_303, c_3857])).
% 6.48/2.29  tff(c_3862, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_3853])).
% 6.48/2.29  tff(c_28, plain, (![A_24]: (k5_relat_1(k6_relat_1(k1_relat_1(A_24)), A_24)=A_24 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.48/2.29  tff(c_93, plain, (![A_24]: (k5_relat_1(k6_partfun1(k1_relat_1(A_24)), A_24)=A_24 | ~v1_relat_1(A_24))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_28])).
% 6.48/2.29  tff(c_3897, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3862, c_93])).
% 6.48/2.29  tff(c_3924, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_158, c_3897])).
% 6.48/2.29  tff(c_72, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_189])).
% 6.48/2.29  tff(c_38, plain, (![A_29]: (k2_relat_1(k2_funct_1(A_29))=k1_relat_1(A_29) | ~v2_funct_1(A_29) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.48/2.29  tff(c_34, plain, (![A_26]: (v1_relat_1(k2_funct_1(A_26)) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.48/2.29  tff(c_44, plain, (![A_30]: (k5_relat_1(A_30, k2_funct_1(A_30))=k6_relat_1(k1_relat_1(A_30)) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.48/2.29  tff(c_90, plain, (![A_30]: (k5_relat_1(A_30, k2_funct_1(A_30))=k6_partfun1(k1_relat_1(A_30)) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_44])).
% 6.48/2.29  tff(c_746, plain, (![B_121]: (k9_relat_1('#skF_3', k1_relat_1(k5_relat_1('#skF_3', B_121)))=k1_relat_1(B_121) | ~r1_tarski(k1_relat_1(B_121), '#skF_2') | ~v1_relat_1(B_121))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_554])).
% 6.48/2.29  tff(c_756, plain, (k9_relat_1('#skF_3', k1_relat_1(k6_partfun1(k1_relat_1('#skF_3'))))=k1_relat_1(k2_funct_1('#skF_3')) | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_90, c_746])).
% 6.48/2.29  tff(c_771, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2' | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_88, c_72, c_567, c_95, c_756])).
% 6.48/2.29  tff(c_907, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_771])).
% 6.48/2.29  tff(c_910, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_907])).
% 6.48/2.29  tff(c_914, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_155, c_88, c_910])).
% 6.48/2.29  tff(c_916, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_771])).
% 6.48/2.29  tff(c_143, plain, (![A_41]: (v1_relat_1(k6_partfun1(A_41)) | ~v1_relat_1(k2_zfmisc_1(A_41, A_41)))), inference(resolution, [status(thm)], [c_89, c_140])).
% 6.48/2.29  tff(c_152, plain, (![A_41]: (v1_relat_1(k6_partfun1(A_41)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_143])).
% 6.48/2.29  tff(c_40, plain, (![A_29]: (k1_relat_1(k2_funct_1(A_29))=k2_relat_1(A_29) | ~v2_funct_1(A_29) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.48/2.29  tff(c_915, plain, (~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2') | k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_771])).
% 6.48/2.29  tff(c_917, plain, (~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2')), inference(splitLeft, [status(thm)], [c_915])).
% 6.48/2.29  tff(c_920, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_40, c_917])).
% 6.48/2.29  tff(c_926, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_155, c_88, c_72, c_6, c_408, c_920])).
% 6.48/2.29  tff(c_927, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_915])).
% 6.48/2.29  tff(c_956, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_927, c_93])).
% 6.48/2.29  tff(c_982, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_916, c_956])).
% 6.48/2.29  tff(c_30, plain, (![A_25]: (k5_relat_1(A_25, k6_relat_1(k2_relat_1(A_25)))=A_25 | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.48/2.29  tff(c_92, plain, (![A_25]: (k5_relat_1(A_25, k6_partfun1(k2_relat_1(A_25)))=A_25 | ~v1_relat_1(A_25))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_30])).
% 6.48/2.29  tff(c_22, plain, (![A_16, B_20, C_22]: (k5_relat_1(k5_relat_1(A_16, B_20), C_22)=k5_relat_1(A_16, k5_relat_1(B_20, C_22)) | ~v1_relat_1(C_22) | ~v1_relat_1(B_20) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.48/2.29  tff(c_1100, plain, (![C_22]: (k5_relat_1(k6_partfun1('#skF_2'), k5_relat_1(k2_funct_1('#skF_3'), C_22))=k5_relat_1(k2_funct_1('#skF_3'), C_22) | ~v1_relat_1(C_22) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k6_partfun1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_982, c_22])).
% 6.48/2.29  tff(c_2546, plain, (![C_215]: (k5_relat_1(k6_partfun1('#skF_2'), k5_relat_1(k2_funct_1('#skF_3'), C_215))=k5_relat_1(k2_funct_1('#skF_3'), C_215) | ~v1_relat_1(C_215))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_916, c_1100])).
% 6.48/2.29  tff(c_2585, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))))=k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3')) | ~v1_relat_1(k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_92, c_2546])).
% 6.48/2.29  tff(c_2599, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_916, c_152, c_982, c_2585])).
% 6.48/2.29  tff(c_2689, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k1_relat_1('#skF_3')))=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_38, c_2599])).
% 6.48/2.29  tff(c_2709, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(k1_relat_1('#skF_3')))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_88, c_72, c_2689])).
% 6.48/2.29  tff(c_3171, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3168, c_2709])).
% 6.48/2.29  tff(c_26, plain, (![A_23]: (k2_relat_1(k6_relat_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.48/2.29  tff(c_94, plain, (![A_23]: (k2_relat_1(k6_partfun1(A_23))=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_26])).
% 6.48/2.29  tff(c_173, plain, (![A_74]: (k5_relat_1(A_74, k6_partfun1(k2_relat_1(A_74)))=A_74 | ~v1_relat_1(A_74))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_30])).
% 6.48/2.29  tff(c_182, plain, (![A_23]: (k5_relat_1(k6_partfun1(A_23), k6_partfun1(A_23))=k6_partfun1(A_23) | ~v1_relat_1(k6_partfun1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_94, c_173])).
% 6.48/2.29  tff(c_186, plain, (![A_23]: (k5_relat_1(k6_partfun1(A_23), k6_partfun1(A_23))=k6_partfun1(A_23))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_182])).
% 6.48/2.29  tff(c_42, plain, (![A_30]: (k5_relat_1(k2_funct_1(A_30), A_30)=k6_relat_1(k2_relat_1(A_30)) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.48/2.29  tff(c_91, plain, (![A_30]: (k5_relat_1(k2_funct_1(A_30), A_30)=k6_partfun1(k2_relat_1(A_30)) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_42])).
% 6.48/2.29  tff(c_2577, plain, (k5_relat_1(k6_partfun1('#skF_2'), k6_partfun1(k2_relat_1('#skF_3')))=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_91, c_2546])).
% 6.48/2.29  tff(c_2595, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_88, c_72, c_155, c_186, c_408, c_2577])).
% 6.48/2.29  tff(c_2621, plain, (![C_22]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_22))=k5_relat_1(k6_partfun1('#skF_2'), C_22) | ~v1_relat_1(C_22) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2595, c_22])).
% 6.48/2.29  tff(c_2637, plain, (![C_22]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_22))=k5_relat_1(k6_partfun1('#skF_2'), C_22) | ~v1_relat_1(C_22))), inference(demodulation, [status(thm), theory('equality')], [c_916, c_155, c_2621])).
% 6.48/2.29  tff(c_3135, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3128, c_2637])).
% 6.48/2.29  tff(c_3151, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_3135])).
% 6.48/2.29  tff(c_4751, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3924, c_3171, c_3151])).
% 6.48/2.29  tff(c_4752, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_4751])).
% 6.48/2.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.48/2.29  
% 6.48/2.29  Inference rules
% 6.48/2.29  ----------------------
% 6.48/2.29  #Ref     : 0
% 6.48/2.29  #Sup     : 1003
% 6.48/2.29  #Fact    : 0
% 6.48/2.29  #Define  : 0
% 6.48/2.29  #Split   : 7
% 6.48/2.29  #Chain   : 0
% 6.48/2.29  #Close   : 0
% 6.48/2.29  
% 6.48/2.29  Ordering : KBO
% 6.48/2.29  
% 6.48/2.29  Simplification rules
% 6.48/2.29  ----------------------
% 6.48/2.29  #Subsume      : 78
% 6.48/2.29  #Demod        : 1653
% 6.48/2.29  #Tautology    : 469
% 6.48/2.29  #SimpNegUnit  : 1
% 6.48/2.29  #BackRed      : 16
% 6.48/2.29  
% 6.48/2.29  #Partial instantiations: 0
% 6.48/2.29  #Strategies tried      : 1
% 6.48/2.29  
% 6.48/2.29  Timing (in seconds)
% 6.48/2.29  ----------------------
% 6.48/2.30  Preprocessing        : 0.37
% 6.48/2.30  Parsing              : 0.20
% 6.48/2.30  CNF conversion       : 0.03
% 6.48/2.30  Main loop            : 1.14
% 6.48/2.30  Inferencing          : 0.38
% 6.48/2.30  Reduction            : 0.46
% 6.48/2.30  Demodulation         : 0.35
% 6.48/2.30  BG Simplification    : 0.04
% 6.48/2.30  Subsumption          : 0.19
% 6.48/2.30  Abstraction          : 0.05
% 6.48/2.30  MUC search           : 0.00
% 6.48/2.30  Cooper               : 0.00
% 6.48/2.30  Total                : 1.56
% 6.48/2.30  Index Insertion      : 0.00
% 6.48/2.30  Index Deletion       : 0.00
% 6.48/2.30  Index Matching       : 0.00
% 6.48/2.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
