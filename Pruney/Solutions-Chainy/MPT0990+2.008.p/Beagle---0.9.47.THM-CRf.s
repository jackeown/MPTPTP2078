%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:56 EST 2020

% Result     : Theorem 9.84s
% Output     : CNFRefutation 9.84s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 851 expanded)
%              Number of leaves         :   51 ( 318 expanded)
%              Depth                    :   16
%              Number of atoms          :  291 (2943 expanded)
%              Number of equality atoms :   81 ( 923 expanded)
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

tff(f_187,negated_conjecture,(
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

tff(f_117,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_123,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_161,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_69,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_149,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_137,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_135,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_159,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_127,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_113,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_103,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_64,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_76,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_161,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_173,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_161])).

tff(c_199,plain,(
    ! [C_72,A_73,B_74] :
      ( v4_relat_1(C_72,A_73)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_211,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_199])).

tff(c_10,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k1_relat_1(B_4),A_3)
      | ~ v4_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_82,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_172,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_161])).

tff(c_210,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_82,c_199])).

tff(c_62,plain,(
    ! [A_53] : k6_relat_1(A_53) = k6_partfun1(A_53) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_20,plain,(
    ! [A_19] : k1_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_93,plain,(
    ! [A_19] : k1_relat_1(k6_partfun1(A_19)) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_20])).

tff(c_86,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_80,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_56,plain,(
    ! [D_44,F_46,C_43,A_41,B_42,E_45] :
      ( m1_subset_1(k1_partfun1(A_41,B_42,C_43,D_44,E_45,F_46),k1_zfmisc_1(k2_zfmisc_1(A_41,D_44)))
      | ~ m1_subset_1(F_46,k1_zfmisc_1(k2_zfmisc_1(C_43,D_44)))
      | ~ v1_funct_1(F_46)
      | ~ m1_subset_1(E_45,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42)))
      | ~ v1_funct_1(E_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_54,plain,(
    ! [A_40] : m1_subset_1(k6_relat_1(A_40),k1_zfmisc_1(k2_zfmisc_1(A_40,A_40))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_87,plain,(
    ! [A_40] : m1_subset_1(k6_partfun1(A_40),k1_zfmisc_1(k2_zfmisc_1(A_40,A_40))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_54])).

tff(c_72,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_1151,plain,(
    ! [D_136,C_137,A_138,B_139] :
      ( D_136 = C_137
      | ~ r2_relset_1(A_138,B_139,C_137,D_136)
      | ~ m1_subset_1(D_136,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139)))
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1159,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_72,c_1151])).

tff(c_1174,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_1159])).

tff(c_1240,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1174])).

tff(c_1758,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_1240])).

tff(c_1762,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_80,c_76,c_1758])).

tff(c_1763,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1174])).

tff(c_1906,plain,(
    ! [B_191,F_188,A_187,E_189,D_190,C_192] :
      ( k1_partfun1(A_187,B_191,C_192,D_190,E_189,F_188) = k5_relat_1(E_189,F_188)
      | ~ m1_subset_1(F_188,k1_zfmisc_1(k2_zfmisc_1(C_192,D_190)))
      | ~ v1_funct_1(F_188)
      | ~ m1_subset_1(E_189,k1_zfmisc_1(k2_zfmisc_1(A_187,B_191)))
      | ~ v1_funct_1(E_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_1912,plain,(
    ! [A_187,B_191,E_189] :
      ( k1_partfun1(A_187,B_191,'#skF_2','#skF_1',E_189,'#skF_4') = k5_relat_1(E_189,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_189,k1_zfmisc_1(k2_zfmisc_1(A_187,B_191)))
      | ~ v1_funct_1(E_189) ) ),
    inference(resolution,[status(thm)],[c_76,c_1906])).

tff(c_2438,plain,(
    ! [A_210,B_211,E_212] :
      ( k1_partfun1(A_210,B_211,'#skF_2','#skF_1',E_212,'#skF_4') = k5_relat_1(E_212,'#skF_4')
      | ~ m1_subset_1(E_212,k1_zfmisc_1(k2_zfmisc_1(A_210,B_211)))
      | ~ v1_funct_1(E_212) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1912])).

tff(c_2453,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_2438])).

tff(c_2467,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1763,c_2453])).

tff(c_16,plain,(
    ! [A_9,B_11] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_9,B_11)),k1_relat_1(A_9))
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2480,plain,
    ( r1_tarski(k1_relat_1(k6_partfun1('#skF_1')),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2467,c_16])).

tff(c_2488,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_173,c_93,c_2480])).

tff(c_245,plain,(
    ! [B_85,A_86] :
      ( r1_tarski(k1_relat_1(B_85),A_86)
      | ~ v4_relat_1(B_85,A_86)
      | ~ v1_relat_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_255,plain,(
    ! [B_85,A_86] :
      ( k1_relat_1(B_85) = A_86
      | ~ r1_tarski(A_86,k1_relat_1(B_85))
      | ~ v4_relat_1(B_85,A_86)
      | ~ v1_relat_1(B_85) ) ),
    inference(resolution,[status(thm)],[c_245,c_2])).

tff(c_2492,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2488,c_255])).

tff(c_2497,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_210,c_2492])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_517,plain,(
    ! [A_108,B_109,C_110] :
      ( k2_relset_1(A_108,B_109,C_110) = k2_relat_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_523,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_517])).

tff(c_530,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_523])).

tff(c_12,plain,(
    ! [A_5] :
      ( k10_relat_1(A_5,k2_relat_1(A_5)) = k1_relat_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_535,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_530,c_12])).

tff(c_542,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_535])).

tff(c_802,plain,(
    ! [B_123,A_124] :
      ( k9_relat_1(B_123,k10_relat_1(B_123,A_124)) = A_124
      | ~ r1_tarski(A_124,k2_relat_1(B_123))
      | ~ v1_funct_1(B_123)
      | ~ v1_relat_1(B_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_804,plain,(
    ! [A_124] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_124)) = A_124
      | ~ r1_tarski(A_124,'#skF_2')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_530,c_802])).

tff(c_829,plain,(
    ! [A_125] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_125)) = A_125
      | ~ r1_tarski(A_125,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_86,c_804])).

tff(c_838,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_542,c_829])).

tff(c_850,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_838])).

tff(c_2501,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2497,c_850])).

tff(c_14,plain,(
    ! [A_6,B_8] :
      ( k10_relat_1(A_6,k1_relat_1(B_8)) = k1_relat_1(k5_relat_1(A_6,B_8))
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_842,plain,(
    ! [B_8] :
      ( k9_relat_1('#skF_3',k1_relat_1(k5_relat_1('#skF_3',B_8))) = k1_relat_1(B_8)
      | ~ r1_tarski(k1_relat_1(B_8),'#skF_2')
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_829])).

tff(c_852,plain,(
    ! [B_8] :
      ( k9_relat_1('#skF_3',k1_relat_1(k5_relat_1('#skF_3',B_8))) = k1_relat_1(B_8)
      | ~ r1_tarski(k1_relat_1(B_8),'#skF_2')
      | ~ v1_relat_1(B_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_842])).

tff(c_2474,plain,
    ( k9_relat_1('#skF_3',k1_relat_1(k6_partfun1('#skF_1'))) = k1_relat_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2467,c_852])).

tff(c_2484,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_93,c_2474])).

tff(c_3141,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2501,c_2484])).

tff(c_3142,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3141])).

tff(c_3146,plain,
    ( ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_3142])).

tff(c_3150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_211,c_3146])).

tff(c_3151,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3141])).

tff(c_24,plain,(
    ! [A_20] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_20)),A_20) = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_91,plain,(
    ! [A_20] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_20)),A_20) = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_24])).

tff(c_3189,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3151,c_91])).

tff(c_3215,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_3189])).

tff(c_70,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_30,plain,(
    ! [A_22] :
      ( v1_relat_1(k2_funct_1(A_22))
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_40,plain,(
    ! [A_26] :
      ( k5_relat_1(A_26,k2_funct_1(A_26)) = k6_relat_1(k1_relat_1(A_26))
      | ~ v2_funct_1(A_26)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_88,plain,(
    ! [A_26] :
      ( k5_relat_1(A_26,k2_funct_1(A_26)) = k6_partfun1(k1_relat_1(A_26))
      | ~ v2_funct_1(A_26)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_40])).

tff(c_1094,plain,(
    ! [B_135] :
      ( k9_relat_1('#skF_3',k1_relat_1(k5_relat_1('#skF_3',B_135))) = k1_relat_1(B_135)
      | ~ r1_tarski(k1_relat_1(B_135),'#skF_2')
      | ~ v1_relat_1(B_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_842])).

tff(c_1107,plain,
    ( k9_relat_1('#skF_3',k1_relat_1(k6_partfun1(k1_relat_1('#skF_3')))) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_1094])).

tff(c_1122,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2'
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_86,c_70,c_850,c_93,c_1107])).

tff(c_1129,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1122])).

tff(c_1132,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_1129])).

tff(c_1136,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_86,c_1132])).

tff(c_1138,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1122])).

tff(c_288,plain,(
    ! [A_90] :
      ( k2_relat_1(k2_funct_1(A_90)) = k1_relat_1(A_90)
      | ~ v2_funct_1(A_90)
      | ~ v1_funct_1(A_90)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_26,plain,(
    ! [A_21] :
      ( k5_relat_1(A_21,k6_relat_1(k2_relat_1(A_21))) = A_21
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_90,plain,(
    ! [A_21] :
      ( k5_relat_1(A_21,k6_partfun1(k2_relat_1(A_21))) = A_21
      | ~ v1_relat_1(A_21) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_26])).

tff(c_3782,plain,(
    ! [A_239] :
      ( k5_relat_1(k2_funct_1(A_239),k6_partfun1(k1_relat_1(A_239))) = k2_funct_1(A_239)
      | ~ v1_relat_1(k2_funct_1(A_239))
      | ~ v2_funct_1(A_239)
      | ~ v1_funct_1(A_239)
      | ~ v1_relat_1(A_239) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_90])).

tff(c_3819,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2497,c_3782])).

tff(c_3856,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_86,c_70,c_1138,c_3819])).

tff(c_38,plain,(
    ! [A_26] :
      ( k5_relat_1(k2_funct_1(A_26),A_26) = k6_relat_1(k2_relat_1(A_26))
      | ~ v2_funct_1(A_26)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_89,plain,(
    ! [A_26] :
      ( k5_relat_1(k2_funct_1(A_26),A_26) = k6_partfun1(k2_relat_1(A_26))
      | ~ v2_funct_1(A_26)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_38])).

tff(c_898,plain,(
    ! [A_128,B_129,C_130] :
      ( k5_relat_1(k5_relat_1(A_128,B_129),C_130) = k5_relat_1(A_128,k5_relat_1(B_129,C_130))
      | ~ v1_relat_1(C_130)
      | ~ v1_relat_1(B_129)
      | ~ v1_relat_1(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_12491,plain,(
    ! [A_371,C_372] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_371)),C_372) = k5_relat_1(k2_funct_1(A_371),k5_relat_1(A_371,C_372))
      | ~ v1_relat_1(C_372)
      | ~ v1_relat_1(A_371)
      | ~ v1_relat_1(k2_funct_1(A_371))
      | ~ v2_funct_1(A_371)
      | ~ v1_funct_1(A_371)
      | ~ v1_relat_1(A_371) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_898])).

tff(c_12757,plain,(
    ! [C_372] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_372)) = k5_relat_1(k6_partfun1('#skF_2'),C_372)
      | ~ v1_relat_1(C_372)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_530,c_12491])).

tff(c_12957,plain,(
    ! [C_374] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_374)) = k5_relat_1(k6_partfun1('#skF_2'),C_374)
      | ~ v1_relat_1(C_374) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_86,c_70,c_1138,c_172,c_12757])).

tff(c_13045,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2467,c_12957])).

tff(c_13101,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_3215,c_3856,c_13045])).

tff(c_13103,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_13101])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:45:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.84/3.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.84/3.63  
% 9.84/3.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.84/3.64  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.84/3.64  
% 9.84/3.64  %Foreground sorts:
% 9.84/3.64  
% 9.84/3.64  
% 9.84/3.64  %Background operators:
% 9.84/3.64  
% 9.84/3.64  
% 9.84/3.64  %Foreground operators:
% 9.84/3.64  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.84/3.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.84/3.64  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.84/3.64  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.84/3.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.84/3.64  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.84/3.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.84/3.64  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.84/3.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.84/3.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.84/3.64  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.84/3.64  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.84/3.64  tff('#skF_2', type, '#skF_2': $i).
% 9.84/3.64  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.84/3.64  tff('#skF_3', type, '#skF_3': $i).
% 9.84/3.64  tff('#skF_1', type, '#skF_1': $i).
% 9.84/3.64  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.84/3.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.84/3.64  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.84/3.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.84/3.64  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 9.84/3.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.84/3.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.84/3.64  tff('#skF_4', type, '#skF_4': $i).
% 9.84/3.64  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.84/3.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.84/3.64  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.84/3.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.84/3.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.84/3.64  
% 9.84/3.66  tff(f_187, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 9.84/3.66  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.84/3.66  tff(f_123, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.84/3.66  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 9.84/3.66  tff(f_161, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.84/3.66  tff(f_69, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 9.84/3.66  tff(f_149, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 9.84/3.66  tff(f_137, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 9.84/3.66  tff(f_135, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 9.84/3.66  tff(f_159, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 9.84/3.66  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 9.84/3.66  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.84/3.66  tff(f_127, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.84/3.66  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 9.84/3.66  tff(f_93, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 9.84/3.66  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 9.84/3.66  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 9.84/3.66  tff(f_85, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 9.84/3.66  tff(f_113, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 9.84/3.66  tff(f_103, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 9.84/3.66  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 9.84/3.66  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 9.84/3.66  tff(c_64, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_187])).
% 9.84/3.66  tff(c_76, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_187])).
% 9.84/3.66  tff(c_161, plain, (![C_66, A_67, B_68]: (v1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.84/3.66  tff(c_173, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_161])).
% 9.84/3.66  tff(c_199, plain, (![C_72, A_73, B_74]: (v4_relat_1(C_72, A_73) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 9.84/3.66  tff(c_211, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_76, c_199])).
% 9.84/3.66  tff(c_10, plain, (![B_4, A_3]: (r1_tarski(k1_relat_1(B_4), A_3) | ~v4_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.84/3.66  tff(c_82, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_187])).
% 9.84/3.66  tff(c_172, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_161])).
% 9.84/3.66  tff(c_210, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_82, c_199])).
% 9.84/3.66  tff(c_62, plain, (![A_53]: (k6_relat_1(A_53)=k6_partfun1(A_53))), inference(cnfTransformation, [status(thm)], [f_161])).
% 9.84/3.66  tff(c_20, plain, (![A_19]: (k1_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.84/3.66  tff(c_93, plain, (![A_19]: (k1_relat_1(k6_partfun1(A_19))=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_20])).
% 9.84/3.66  tff(c_86, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_187])).
% 9.84/3.66  tff(c_80, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_187])).
% 9.84/3.66  tff(c_56, plain, (![D_44, F_46, C_43, A_41, B_42, E_45]: (m1_subset_1(k1_partfun1(A_41, B_42, C_43, D_44, E_45, F_46), k1_zfmisc_1(k2_zfmisc_1(A_41, D_44))) | ~m1_subset_1(F_46, k1_zfmisc_1(k2_zfmisc_1(C_43, D_44))) | ~v1_funct_1(F_46) | ~m1_subset_1(E_45, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))) | ~v1_funct_1(E_45))), inference(cnfTransformation, [status(thm)], [f_149])).
% 9.84/3.66  tff(c_54, plain, (![A_40]: (m1_subset_1(k6_relat_1(A_40), k1_zfmisc_1(k2_zfmisc_1(A_40, A_40))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.84/3.66  tff(c_87, plain, (![A_40]: (m1_subset_1(k6_partfun1(A_40), k1_zfmisc_1(k2_zfmisc_1(A_40, A_40))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_54])).
% 9.84/3.66  tff(c_72, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_187])).
% 9.84/3.66  tff(c_1151, plain, (![D_136, C_137, A_138, B_139]: (D_136=C_137 | ~r2_relset_1(A_138, B_139, C_137, D_136) | ~m1_subset_1(D_136, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 9.84/3.66  tff(c_1159, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_72, c_1151])).
% 9.84/3.66  tff(c_1174, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_1159])).
% 9.84/3.66  tff(c_1240, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1174])).
% 9.84/3.66  tff(c_1758, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_1240])).
% 9.84/3.66  tff(c_1762, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_80, c_76, c_1758])).
% 9.84/3.66  tff(c_1763, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1174])).
% 9.84/3.66  tff(c_1906, plain, (![B_191, F_188, A_187, E_189, D_190, C_192]: (k1_partfun1(A_187, B_191, C_192, D_190, E_189, F_188)=k5_relat_1(E_189, F_188) | ~m1_subset_1(F_188, k1_zfmisc_1(k2_zfmisc_1(C_192, D_190))) | ~v1_funct_1(F_188) | ~m1_subset_1(E_189, k1_zfmisc_1(k2_zfmisc_1(A_187, B_191))) | ~v1_funct_1(E_189))), inference(cnfTransformation, [status(thm)], [f_159])).
% 9.84/3.66  tff(c_1912, plain, (![A_187, B_191, E_189]: (k1_partfun1(A_187, B_191, '#skF_2', '#skF_1', E_189, '#skF_4')=k5_relat_1(E_189, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_189, k1_zfmisc_1(k2_zfmisc_1(A_187, B_191))) | ~v1_funct_1(E_189))), inference(resolution, [status(thm)], [c_76, c_1906])).
% 9.84/3.66  tff(c_2438, plain, (![A_210, B_211, E_212]: (k1_partfun1(A_210, B_211, '#skF_2', '#skF_1', E_212, '#skF_4')=k5_relat_1(E_212, '#skF_4') | ~m1_subset_1(E_212, k1_zfmisc_1(k2_zfmisc_1(A_210, B_211))) | ~v1_funct_1(E_212))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1912])).
% 9.84/3.66  tff(c_2453, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_2438])).
% 9.84/3.66  tff(c_2467, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1763, c_2453])).
% 9.84/3.66  tff(c_16, plain, (![A_9, B_11]: (r1_tarski(k1_relat_1(k5_relat_1(A_9, B_11)), k1_relat_1(A_9)) | ~v1_relat_1(B_11) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.84/3.66  tff(c_2480, plain, (r1_tarski(k1_relat_1(k6_partfun1('#skF_1')), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2467, c_16])).
% 9.84/3.66  tff(c_2488, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_173, c_93, c_2480])).
% 9.84/3.66  tff(c_245, plain, (![B_85, A_86]: (r1_tarski(k1_relat_1(B_85), A_86) | ~v4_relat_1(B_85, A_86) | ~v1_relat_1(B_85))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.84/3.66  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.84/3.66  tff(c_255, plain, (![B_85, A_86]: (k1_relat_1(B_85)=A_86 | ~r1_tarski(A_86, k1_relat_1(B_85)) | ~v4_relat_1(B_85, A_86) | ~v1_relat_1(B_85))), inference(resolution, [status(thm)], [c_245, c_2])).
% 9.84/3.66  tff(c_2492, plain, (k1_relat_1('#skF_3')='#skF_1' | ~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2488, c_255])).
% 9.84/3.66  tff(c_2497, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_172, c_210, c_2492])).
% 9.84/3.66  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.84/3.66  tff(c_74, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_187])).
% 9.84/3.66  tff(c_517, plain, (![A_108, B_109, C_110]: (k2_relset_1(A_108, B_109, C_110)=k2_relat_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.84/3.66  tff(c_523, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_517])).
% 9.84/3.66  tff(c_530, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_523])).
% 9.84/3.66  tff(c_12, plain, (![A_5]: (k10_relat_1(A_5, k2_relat_1(A_5))=k1_relat_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.84/3.66  tff(c_535, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_530, c_12])).
% 9.84/3.66  tff(c_542, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_172, c_535])).
% 9.84/3.66  tff(c_802, plain, (![B_123, A_124]: (k9_relat_1(B_123, k10_relat_1(B_123, A_124))=A_124 | ~r1_tarski(A_124, k2_relat_1(B_123)) | ~v1_funct_1(B_123) | ~v1_relat_1(B_123))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.84/3.66  tff(c_804, plain, (![A_124]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_124))=A_124 | ~r1_tarski(A_124, '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_530, c_802])).
% 9.84/3.66  tff(c_829, plain, (![A_125]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_125))=A_125 | ~r1_tarski(A_125, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_86, c_804])).
% 9.84/3.66  tff(c_838, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_2' | ~r1_tarski('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_542, c_829])).
% 9.84/3.66  tff(c_850, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_838])).
% 9.84/3.66  tff(c_2501, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2497, c_850])).
% 9.84/3.66  tff(c_14, plain, (![A_6, B_8]: (k10_relat_1(A_6, k1_relat_1(B_8))=k1_relat_1(k5_relat_1(A_6, B_8)) | ~v1_relat_1(B_8) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.84/3.66  tff(c_842, plain, (![B_8]: (k9_relat_1('#skF_3', k1_relat_1(k5_relat_1('#skF_3', B_8)))=k1_relat_1(B_8) | ~r1_tarski(k1_relat_1(B_8), '#skF_2') | ~v1_relat_1(B_8) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_829])).
% 9.84/3.66  tff(c_852, plain, (![B_8]: (k9_relat_1('#skF_3', k1_relat_1(k5_relat_1('#skF_3', B_8)))=k1_relat_1(B_8) | ~r1_tarski(k1_relat_1(B_8), '#skF_2') | ~v1_relat_1(B_8))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_842])).
% 9.84/3.66  tff(c_2474, plain, (k9_relat_1('#skF_3', k1_relat_1(k6_partfun1('#skF_1')))=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2467, c_852])).
% 9.84/3.66  tff(c_2484, plain, (k9_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_93, c_2474])).
% 9.84/3.66  tff(c_3141, plain, (k1_relat_1('#skF_4')='#skF_2' | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2501, c_2484])).
% 9.84/3.66  tff(c_3142, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(splitLeft, [status(thm)], [c_3141])).
% 9.84/3.66  tff(c_3146, plain, (~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_3142])).
% 9.84/3.66  tff(c_3150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_173, c_211, c_3146])).
% 9.84/3.66  tff(c_3151, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_3141])).
% 9.84/3.66  tff(c_24, plain, (![A_20]: (k5_relat_1(k6_relat_1(k1_relat_1(A_20)), A_20)=A_20 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.84/3.66  tff(c_91, plain, (![A_20]: (k5_relat_1(k6_partfun1(k1_relat_1(A_20)), A_20)=A_20 | ~v1_relat_1(A_20))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_24])).
% 9.84/3.66  tff(c_3189, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3151, c_91])).
% 9.84/3.66  tff(c_3215, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_173, c_3189])).
% 9.84/3.66  tff(c_70, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_187])).
% 9.84/3.66  tff(c_30, plain, (![A_22]: (v1_relat_1(k2_funct_1(A_22)) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.84/3.66  tff(c_40, plain, (![A_26]: (k5_relat_1(A_26, k2_funct_1(A_26))=k6_relat_1(k1_relat_1(A_26)) | ~v2_funct_1(A_26) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.84/3.66  tff(c_88, plain, (![A_26]: (k5_relat_1(A_26, k2_funct_1(A_26))=k6_partfun1(k1_relat_1(A_26)) | ~v2_funct_1(A_26) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_40])).
% 9.84/3.66  tff(c_1094, plain, (![B_135]: (k9_relat_1('#skF_3', k1_relat_1(k5_relat_1('#skF_3', B_135)))=k1_relat_1(B_135) | ~r1_tarski(k1_relat_1(B_135), '#skF_2') | ~v1_relat_1(B_135))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_842])).
% 9.84/3.66  tff(c_1107, plain, (k9_relat_1('#skF_3', k1_relat_1(k6_partfun1(k1_relat_1('#skF_3'))))=k1_relat_1(k2_funct_1('#skF_3')) | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_88, c_1094])).
% 9.84/3.66  tff(c_1122, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2' | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_86, c_70, c_850, c_93, c_1107])).
% 9.84/3.66  tff(c_1129, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1122])).
% 9.84/3.66  tff(c_1132, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_1129])).
% 9.84/3.66  tff(c_1136, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_172, c_86, c_1132])).
% 9.84/3.66  tff(c_1138, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1122])).
% 9.84/3.66  tff(c_288, plain, (![A_90]: (k2_relat_1(k2_funct_1(A_90))=k1_relat_1(A_90) | ~v2_funct_1(A_90) | ~v1_funct_1(A_90) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.84/3.66  tff(c_26, plain, (![A_21]: (k5_relat_1(A_21, k6_relat_1(k2_relat_1(A_21)))=A_21 | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.84/3.66  tff(c_90, plain, (![A_21]: (k5_relat_1(A_21, k6_partfun1(k2_relat_1(A_21)))=A_21 | ~v1_relat_1(A_21))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_26])).
% 9.84/3.66  tff(c_3782, plain, (![A_239]: (k5_relat_1(k2_funct_1(A_239), k6_partfun1(k1_relat_1(A_239)))=k2_funct_1(A_239) | ~v1_relat_1(k2_funct_1(A_239)) | ~v2_funct_1(A_239) | ~v1_funct_1(A_239) | ~v1_relat_1(A_239))), inference(superposition, [status(thm), theory('equality')], [c_288, c_90])).
% 9.84/3.66  tff(c_3819, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2497, c_3782])).
% 9.84/3.66  tff(c_3856, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_172, c_86, c_70, c_1138, c_3819])).
% 9.84/3.66  tff(c_38, plain, (![A_26]: (k5_relat_1(k2_funct_1(A_26), A_26)=k6_relat_1(k2_relat_1(A_26)) | ~v2_funct_1(A_26) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.84/3.66  tff(c_89, plain, (![A_26]: (k5_relat_1(k2_funct_1(A_26), A_26)=k6_partfun1(k2_relat_1(A_26)) | ~v2_funct_1(A_26) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_38])).
% 9.84/3.66  tff(c_898, plain, (![A_128, B_129, C_130]: (k5_relat_1(k5_relat_1(A_128, B_129), C_130)=k5_relat_1(A_128, k5_relat_1(B_129, C_130)) | ~v1_relat_1(C_130) | ~v1_relat_1(B_129) | ~v1_relat_1(A_128))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.84/3.66  tff(c_12491, plain, (![A_371, C_372]: (k5_relat_1(k6_partfun1(k2_relat_1(A_371)), C_372)=k5_relat_1(k2_funct_1(A_371), k5_relat_1(A_371, C_372)) | ~v1_relat_1(C_372) | ~v1_relat_1(A_371) | ~v1_relat_1(k2_funct_1(A_371)) | ~v2_funct_1(A_371) | ~v1_funct_1(A_371) | ~v1_relat_1(A_371))), inference(superposition, [status(thm), theory('equality')], [c_89, c_898])).
% 9.84/3.66  tff(c_12757, plain, (![C_372]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_372))=k5_relat_1(k6_partfun1('#skF_2'), C_372) | ~v1_relat_1(C_372) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_530, c_12491])).
% 9.84/3.66  tff(c_12957, plain, (![C_374]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_374))=k5_relat_1(k6_partfun1('#skF_2'), C_374) | ~v1_relat_1(C_374))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_86, c_70, c_1138, c_172, c_12757])).
% 9.84/3.66  tff(c_13045, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2467, c_12957])).
% 9.84/3.66  tff(c_13101, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_173, c_3215, c_3856, c_13045])).
% 9.84/3.66  tff(c_13103, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_13101])).
% 9.84/3.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.84/3.66  
% 9.84/3.66  Inference rules
% 9.84/3.66  ----------------------
% 9.84/3.66  #Ref     : 0
% 9.84/3.66  #Sup     : 2820
% 9.84/3.66  #Fact    : 0
% 9.84/3.66  #Define  : 0
% 9.84/3.66  #Split   : 13
% 9.84/3.66  #Chain   : 0
% 9.84/3.66  #Close   : 0
% 9.84/3.66  
% 9.84/3.66  Ordering : KBO
% 9.84/3.66  
% 9.84/3.66  Simplification rules
% 9.84/3.66  ----------------------
% 9.84/3.66  #Subsume      : 223
% 9.84/3.66  #Demod        : 5245
% 9.84/3.66  #Tautology    : 1095
% 9.84/3.66  #SimpNegUnit  : 2
% 9.84/3.66  #BackRed      : 40
% 9.84/3.66  
% 9.84/3.66  #Partial instantiations: 0
% 9.84/3.66  #Strategies tried      : 1
% 9.84/3.66  
% 9.84/3.66  Timing (in seconds)
% 9.84/3.66  ----------------------
% 9.84/3.66  Preprocessing        : 0.37
% 9.84/3.66  Parsing              : 0.20
% 9.84/3.66  CNF conversion       : 0.03
% 9.84/3.66  Main loop            : 2.50
% 9.84/3.66  Inferencing          : 0.63
% 9.84/3.66  Reduction            : 1.21
% 9.84/3.66  Demodulation         : 1.00
% 9.84/3.66  BG Simplification    : 0.07
% 9.84/3.66  Subsumption          : 0.47
% 9.84/3.66  Abstraction          : 0.09
% 9.84/3.66  MUC search           : 0.00
% 9.84/3.66  Cooper               : 0.00
% 9.84/3.66  Total                : 2.92
% 9.84/3.66  Index Insertion      : 0.00
% 9.84/3.66  Index Deletion       : 0.00
% 9.84/3.66  Index Matching       : 0.00
% 9.84/3.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
