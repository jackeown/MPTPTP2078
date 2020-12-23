%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:56 EST 2020

% Result     : Theorem 56.82s
% Output     : CNFRefutation 56.82s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 964 expanded)
%              Number of leaves         :   50 ( 360 expanded)
%              Depth                    :   18
%              Number of atoms          :  390 (3582 expanded)
%              Number of equality atoms :  126 (1152 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_204,negated_conjecture,(
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

tff(f_117,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_123,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_161,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_127,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_149,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_137,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_135,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_159,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & k2_relat_1(B) = k1_relat_1(A) )
           => ( v2_funct_1(B)
              & v2_funct_1(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_59,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_55,axiom,(
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

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_105,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(B) = k1_relat_1(A)
              & k5_relat_1(B,A) = k6_relat_1(k2_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_178,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
           => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_113,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(c_60,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_125,plain,(
    ! [C_63,A_64,B_65] :
      ( v1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_138,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_125])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_232,plain,(
    ! [C_84,A_85,B_86] :
      ( v4_relat_1(C_84,A_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_245,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_232])).

tff(c_10,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k1_relat_1(B_4),A_3)
      | ~ v4_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_78,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_137,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_125])).

tff(c_82,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_56,plain,(
    ! [A_49] : k6_relat_1(A_49) = k6_partfun1(A_49) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_24,plain,(
    ! [A_13] : v2_funct_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_85,plain,(
    ! [A_13] : v2_funct_1(k6_partfun1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_24])).

tff(c_70,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_372,plain,(
    ! [A_104,B_105,C_106] :
      ( k2_relset_1(A_104,B_105,C_106) = k2_relat_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_378,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_372])).

tff(c_385,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_378])).

tff(c_1146,plain,(
    ! [C_209,F_206,B_205,D_207,A_204,E_208] :
      ( m1_subset_1(k1_partfun1(A_204,B_205,C_209,D_207,E_208,F_206),k1_zfmisc_1(k2_zfmisc_1(A_204,D_207)))
      | ~ m1_subset_1(F_206,k1_zfmisc_1(k2_zfmisc_1(C_209,D_207)))
      | ~ v1_funct_1(F_206)
      | ~ m1_subset_1(E_208,k1_zfmisc_1(k2_zfmisc_1(A_204,B_205)))
      | ~ v1_funct_1(E_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_48,plain,(
    ! [A_36] : m1_subset_1(k6_relat_1(A_36),k1_zfmisc_1(k2_zfmisc_1(A_36,A_36))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_83,plain,(
    ! [A_36] : m1_subset_1(k6_partfun1(A_36),k1_zfmisc_1(k2_zfmisc_1(A_36,A_36))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_48])).

tff(c_68,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_730,plain,(
    ! [D_146,C_147,A_148,B_149] :
      ( D_146 = C_147
      | ~ r2_relset_1(A_148,B_149,C_147,D_146)
      | ~ m1_subset_1(D_146,k1_zfmisc_1(k2_zfmisc_1(A_148,B_149)))
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_148,B_149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_738,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_68,c_730])).

tff(c_753,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_738])).

tff(c_827,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_753])).

tff(c_1162,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1146,c_827])).

tff(c_1191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_76,c_72,c_1162])).

tff(c_1192,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_753])).

tff(c_1808,plain,(
    ! [D_264,C_263,B_267,A_266,F_265,E_268] :
      ( k1_partfun1(A_266,B_267,C_263,D_264,E_268,F_265) = k5_relat_1(E_268,F_265)
      | ~ m1_subset_1(F_265,k1_zfmisc_1(k2_zfmisc_1(C_263,D_264)))
      | ~ v1_funct_1(F_265)
      | ~ m1_subset_1(E_268,k1_zfmisc_1(k2_zfmisc_1(A_266,B_267)))
      | ~ v1_funct_1(E_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_1814,plain,(
    ! [A_266,B_267,E_268] :
      ( k1_partfun1(A_266,B_267,'#skF_2','#skF_1',E_268,'#skF_4') = k5_relat_1(E_268,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_268,k1_zfmisc_1(k2_zfmisc_1(A_266,B_267)))
      | ~ v1_funct_1(E_268) ) ),
    inference(resolution,[status(thm)],[c_72,c_1808])).

tff(c_1884,plain,(
    ! [A_272,B_273,E_274] :
      ( k1_partfun1(A_272,B_273,'#skF_2','#skF_1',E_274,'#skF_4') = k5_relat_1(E_274,'#skF_4')
      | ~ m1_subset_1(E_274,k1_zfmisc_1(k2_zfmisc_1(A_272,B_273)))
      | ~ v1_funct_1(E_274) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1814])).

tff(c_1890,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_1884])).

tff(c_1897,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1192,c_1890])).

tff(c_28,plain,(
    ! [A_16,B_18] :
      ( v2_funct_1(A_16)
      | k2_relat_1(B_18) != k1_relat_1(A_16)
      | ~ v2_funct_1(k5_relat_1(B_18,A_16))
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1907,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1897,c_28])).

tff(c_1925,plain,
    ( v2_funct_1('#skF_4')
    | k1_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_76,c_137,c_82,c_85,c_385,c_1907])).

tff(c_2079,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1925])).

tff(c_244,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_78,c_232])).

tff(c_18,plain,(
    ! [A_12] : k1_relat_1(k6_relat_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_88,plain,(
    ! [A_12] : k1_relat_1(k6_partfun1(A_12)) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_18])).

tff(c_16,plain,(
    ! [A_9,B_11] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_9,B_11)),k1_relat_1(A_9))
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_169,plain,(
    ! [B_70,A_71] :
      ( r1_tarski(k1_relat_1(B_70),A_71)
      | ~ v4_relat_1(B_70,A_71)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_416,plain,(
    ! [B_110,A_111] :
      ( k1_relat_1(B_110) = A_111
      | ~ r1_tarski(A_111,k1_relat_1(B_110))
      | ~ v4_relat_1(B_110,A_111)
      | ~ v1_relat_1(B_110) ) ),
    inference(resolution,[status(thm)],[c_169,c_2])).

tff(c_448,plain,(
    ! [A_9,B_11] :
      ( k1_relat_1(k5_relat_1(A_9,B_11)) = k1_relat_1(A_9)
      | ~ v4_relat_1(A_9,k1_relat_1(k5_relat_1(A_9,B_11)))
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_9) ) ),
    inference(resolution,[status(thm)],[c_16,c_416])).

tff(c_1904,plain,
    ( k1_relat_1(k5_relat_1('#skF_3','#skF_4')) = k1_relat_1('#skF_3')
    | ~ v4_relat_1('#skF_3',k1_relat_1(k6_partfun1('#skF_1')))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1897,c_448])).

tff(c_1923,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_138,c_244,c_88,c_88,c_1897,c_1904])).

tff(c_12,plain,(
    ! [A_5] :
      ( k9_relat_1(A_5,k1_relat_1(A_5)) = k2_relat_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1983,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1923,c_12])).

tff(c_2011,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_385,c_1983])).

tff(c_14,plain,(
    ! [A_6,B_8] :
      ( k10_relat_1(A_6,k1_relat_1(B_8)) = k1_relat_1(k5_relat_1(A_6,B_8))
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_454,plain,(
    ! [B_112,A_113] :
      ( k9_relat_1(B_112,k10_relat_1(B_112,A_113)) = A_113
      | ~ r1_tarski(A_113,k2_relat_1(B_112))
      | ~ v1_funct_1(B_112)
      | ~ v1_relat_1(B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_456,plain,(
    ! [A_113] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_113)) = A_113
      | ~ r1_tarski(A_113,'#skF_2')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_385,c_454])).

tff(c_498,plain,(
    ! [A_116] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_116)) = A_116
      | ~ r1_tarski(A_116,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_82,c_456])).

tff(c_508,plain,(
    ! [B_8] :
      ( k9_relat_1('#skF_3',k1_relat_1(k5_relat_1('#skF_3',B_8))) = k1_relat_1(B_8)
      | ~ r1_tarski(k1_relat_1(B_8),'#skF_2')
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_498])).

tff(c_512,plain,(
    ! [B_8] :
      ( k9_relat_1('#skF_3',k1_relat_1(k5_relat_1('#skF_3',B_8))) = k1_relat_1(B_8)
      | ~ r1_tarski(k1_relat_1(B_8),'#skF_2')
      | ~ v1_relat_1(B_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_508])).

tff(c_1910,plain,
    ( k9_relat_1('#skF_3',k1_relat_1(k6_partfun1('#skF_1'))) = k1_relat_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1897,c_512])).

tff(c_1927,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_88,c_1910])).

tff(c_2671,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2011,c_1927])).

tff(c_2672,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_2079,c_2671])).

tff(c_2675,plain,
    ( ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_2672])).

tff(c_2679,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_245,c_2675])).

tff(c_2680,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1925])).

tff(c_2681,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1925])).

tff(c_1223,plain,(
    ! [E_216,F_214,D_215,C_217,B_213,A_212] :
      ( v1_funct_1(k1_partfun1(A_212,B_213,C_217,D_215,E_216,F_214))
      | ~ m1_subset_1(F_214,k1_zfmisc_1(k2_zfmisc_1(C_217,D_215)))
      | ~ v1_funct_1(F_214)
      | ~ m1_subset_1(E_216,k1_zfmisc_1(k2_zfmisc_1(A_212,B_213)))
      | ~ v1_funct_1(E_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1229,plain,(
    ! [A_212,B_213,E_216] :
      ( v1_funct_1(k1_partfun1(A_212,B_213,'#skF_2','#skF_1',E_216,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_216,k1_zfmisc_1(k2_zfmisc_1(A_212,B_213)))
      | ~ v1_funct_1(E_216) ) ),
    inference(resolution,[status(thm)],[c_72,c_1223])).

tff(c_1276,plain,(
    ! [A_226,B_227,E_228] :
      ( v1_funct_1(k1_partfun1(A_226,B_227,'#skF_2','#skF_1',E_228,'#skF_4'))
      | ~ m1_subset_1(E_228,k1_zfmisc_1(k2_zfmisc_1(A_226,B_227)))
      | ~ v1_funct_1(E_228) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1229])).

tff(c_1282,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_1276])).

tff(c_1289,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1192,c_1282])).

tff(c_20,plain,(
    ! [A_12] : k2_relat_1(k6_relat_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_87,plain,(
    ! [A_12] : k2_relat_1(k6_partfun1(A_12)) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_20])).

tff(c_22,plain,(
    ! [A_13] : v1_relat_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_86,plain,(
    ! [A_13] : v1_relat_1(k6_partfun1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_22])).

tff(c_66,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_32,plain,(
    ! [A_19,B_21] :
      ( k2_funct_1(A_19) = B_21
      | k6_relat_1(k2_relat_1(A_19)) != k5_relat_1(B_21,A_19)
      | k2_relat_1(B_21) != k1_relat_1(A_19)
      | ~ v2_funct_1(A_19)
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1267,plain,(
    ! [A_224,B_225] :
      ( k2_funct_1(A_224) = B_225
      | k6_partfun1(k2_relat_1(A_224)) != k5_relat_1(B_225,A_224)
      | k2_relat_1(B_225) != k1_relat_1(A_224)
      | ~ v2_funct_1(A_224)
      | ~ v1_funct_1(B_225)
      | ~ v1_relat_1(B_225)
      | ~ v1_funct_1(A_224)
      | ~ v1_relat_1(A_224) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_32])).

tff(c_1269,plain,(
    ! [B_225] :
      ( k2_funct_1('#skF_3') = B_225
      | k5_relat_1(B_225,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_225) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_225)
      | ~ v1_relat_1(B_225)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_385,c_1267])).

tff(c_1294,plain,(
    ! [B_230] :
      ( k2_funct_1('#skF_3') = B_230
      | k5_relat_1(B_230,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_230) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_230)
      | ~ v1_relat_1(B_230) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_82,c_66,c_1269])).

tff(c_1303,plain,(
    ! [A_13] :
      ( k6_partfun1(A_13) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_13),'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(k6_partfun1(A_13)) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(k6_partfun1(A_13)) ) ),
    inference(resolution,[status(thm)],[c_86,c_1294])).

tff(c_1330,plain,(
    ! [A_237] :
      ( k6_partfun1(A_237) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_237),'#skF_3') != k6_partfun1('#skF_2')
      | k1_relat_1('#skF_3') != A_237
      | ~ v1_funct_1(k6_partfun1(A_237)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_1303])).

tff(c_1334,plain,
    ( k6_partfun1('#skF_1') = k2_funct_1('#skF_3')
    | k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_1289,c_1330])).

tff(c_1335,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1334])).

tff(c_1315,plain,(
    ! [A_234,C_231,D_232,E_236,B_235,F_233] :
      ( k1_partfun1(A_234,B_235,C_231,D_232,E_236,F_233) = k5_relat_1(E_236,F_233)
      | ~ m1_subset_1(F_233,k1_zfmisc_1(k2_zfmisc_1(C_231,D_232)))
      | ~ v1_funct_1(F_233)
      | ~ m1_subset_1(E_236,k1_zfmisc_1(k2_zfmisc_1(A_234,B_235)))
      | ~ v1_funct_1(E_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_1321,plain,(
    ! [A_234,B_235,E_236] :
      ( k1_partfun1(A_234,B_235,'#skF_2','#skF_1',E_236,'#skF_4') = k5_relat_1(E_236,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_236,k1_zfmisc_1(k2_zfmisc_1(A_234,B_235)))
      | ~ v1_funct_1(E_236) ) ),
    inference(resolution,[status(thm)],[c_72,c_1315])).

tff(c_1336,plain,(
    ! [A_238,B_239,E_240] :
      ( k1_partfun1(A_238,B_239,'#skF_2','#skF_1',E_240,'#skF_4') = k5_relat_1(E_240,'#skF_4')
      | ~ m1_subset_1(E_240,k1_zfmisc_1(k2_zfmisc_1(A_238,B_239)))
      | ~ v1_funct_1(E_240) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1321])).

tff(c_1342,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_1336])).

tff(c_1349,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1192,c_1342])).

tff(c_1356,plain,
    ( k1_relat_1(k5_relat_1('#skF_3','#skF_4')) = k1_relat_1('#skF_3')
    | ~ v4_relat_1('#skF_3',k1_relat_1(k6_partfun1('#skF_1')))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1349,c_448])).

tff(c_1375,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_138,c_244,c_88,c_88,c_1349,c_1356])).

tff(c_1377,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1335,c_1375])).

tff(c_1379,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1334])).

tff(c_1297,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_138,c_1294])).

tff(c_1306,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1297])).

tff(c_1307,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1306])).

tff(c_1313,plain,(
    k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1307])).

tff(c_1382,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1379,c_1313])).

tff(c_74,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_80,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_284,plain,(
    ! [A_92,B_93,D_94] :
      ( r2_relset_1(A_92,B_93,D_94,D_94)
      | ~ m1_subset_1(D_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_291,plain,(
    ! [A_36] : r2_relset_1(A_36,A_36,k6_partfun1(A_36),k6_partfun1(A_36)) ),
    inference(resolution,[status(thm)],[c_83,c_284])).

tff(c_386,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_372])).

tff(c_1711,plain,(
    ! [A_257,B_258,C_259,D_260] :
      ( k2_relset_1(A_257,B_258,C_259) = B_258
      | ~ r2_relset_1(B_258,B_258,k1_partfun1(B_258,A_257,A_257,B_258,D_260,C_259),k6_partfun1(B_258))
      | ~ m1_subset_1(D_260,k1_zfmisc_1(k2_zfmisc_1(B_258,A_257)))
      | ~ v1_funct_2(D_260,B_258,A_257)
      | ~ v1_funct_1(D_260)
      | ~ m1_subset_1(C_259,k1_zfmisc_1(k2_zfmisc_1(A_257,B_258)))
      | ~ v1_funct_2(C_259,A_257,B_258)
      | ~ v1_funct_1(C_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_1714,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1192,c_1711])).

tff(c_1716,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_82,c_80,c_78,c_291,c_386,c_1714])).

tff(c_1718,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1382,c_1716])).

tff(c_1720,plain,(
    k2_relat_1('#skF_4') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1307])).

tff(c_1943,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1923,c_1720])).

tff(c_84,plain,(
    ! [A_19,B_21] :
      ( k2_funct_1(A_19) = B_21
      | k6_partfun1(k2_relat_1(A_19)) != k5_relat_1(B_21,A_19)
      | k2_relat_1(B_21) != k1_relat_1(A_19)
      | ~ v2_funct_1(A_19)
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_32])).

tff(c_2015,plain,(
    ! [B_21] :
      ( k2_funct_1('#skF_4') = B_21
      | k5_relat_1(B_21,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_21) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1943,c_84])).

tff(c_2024,plain,(
    ! [B_21] :
      ( k2_funct_1('#skF_4') = B_21
      | k5_relat_1(B_21,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_21) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_76,c_2015])).

tff(c_67393,plain,(
    ! [B_1616] :
      ( k2_funct_1('#skF_4') = B_1616
      | k5_relat_1(B_1616,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_1616) != '#skF_2'
      | ~ v1_funct_1(B_1616)
      | ~ v1_relat_1(B_1616) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2680,c_2681,c_2024])).

tff(c_67939,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_137,c_67393])).

tff(c_68372,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_385,c_1897,c_67939])).

tff(c_34,plain,(
    ! [A_22] :
      ( k2_funct_1(k2_funct_1(A_22)) = A_22
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_68379,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_68372,c_34])).

tff(c_68383,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_76,c_2680,c_68379])).

tff(c_68385,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_68383])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:38:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 56.82/45.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 56.82/45.33  
% 56.82/45.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 56.82/45.34  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 56.82/45.34  
% 56.82/45.34  %Foreground sorts:
% 56.82/45.34  
% 56.82/45.34  
% 56.82/45.34  %Background operators:
% 56.82/45.34  
% 56.82/45.34  
% 56.82/45.34  %Foreground operators:
% 56.82/45.34  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 56.82/45.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 56.82/45.34  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 56.82/45.34  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 56.82/45.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 56.82/45.34  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 56.82/45.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 56.82/45.34  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 56.82/45.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 56.82/45.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 56.82/45.34  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 56.82/45.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 56.82/45.34  tff('#skF_2', type, '#skF_2': $i).
% 56.82/45.34  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 56.82/45.34  tff('#skF_3', type, '#skF_3': $i).
% 56.82/45.34  tff('#skF_1', type, '#skF_1': $i).
% 56.82/45.34  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 56.82/45.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 56.82/45.34  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 56.82/45.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 56.82/45.34  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 56.82/45.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 56.82/45.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 56.82/45.34  tff('#skF_4', type, '#skF_4': $i).
% 56.82/45.34  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 56.82/45.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 56.82/45.34  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 56.82/45.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 56.82/45.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 56.82/45.34  
% 56.82/45.36  tff(f_204, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 56.82/45.36  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 56.82/45.36  tff(f_123, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 56.82/45.36  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 56.82/45.36  tff(f_161, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 56.82/45.36  tff(f_63, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 56.82/45.36  tff(f_127, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 56.82/45.36  tff(f_149, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 56.82/45.36  tff(f_137, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 56.82/45.36  tff(f_135, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 56.82/45.36  tff(f_159, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 56.82/45.36  tff(f_88, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 56.82/45.36  tff(f_59, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 56.82/45.36  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 56.82/45.36  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 56.82/45.36  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 56.82/45.36  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 56.82/45.36  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 56.82/45.36  tff(f_105, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 56.82/45.36  tff(f_178, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 56.82/45.36  tff(f_113, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 56.82/45.36  tff(c_60, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_204])).
% 56.82/45.36  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_204])).
% 56.82/45.36  tff(c_125, plain, (![C_63, A_64, B_65]: (v1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 56.82/45.36  tff(c_138, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_125])).
% 56.82/45.36  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_204])).
% 56.82/45.36  tff(c_232, plain, (![C_84, A_85, B_86]: (v4_relat_1(C_84, A_85) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 56.82/45.36  tff(c_245, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_232])).
% 56.82/45.36  tff(c_10, plain, (![B_4, A_3]: (r1_tarski(k1_relat_1(B_4), A_3) | ~v4_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 56.82/45.36  tff(c_78, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_204])).
% 56.82/45.36  tff(c_137, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_125])).
% 56.82/45.36  tff(c_82, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_204])).
% 56.82/45.36  tff(c_56, plain, (![A_49]: (k6_relat_1(A_49)=k6_partfun1(A_49))), inference(cnfTransformation, [status(thm)], [f_161])).
% 56.82/45.36  tff(c_24, plain, (![A_13]: (v2_funct_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 56.82/45.36  tff(c_85, plain, (![A_13]: (v2_funct_1(k6_partfun1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_24])).
% 56.82/45.36  tff(c_70, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_204])).
% 56.82/45.36  tff(c_372, plain, (![A_104, B_105, C_106]: (k2_relset_1(A_104, B_105, C_106)=k2_relat_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 56.82/45.36  tff(c_378, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_372])).
% 56.82/45.36  tff(c_385, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_378])).
% 56.82/45.36  tff(c_1146, plain, (![C_209, F_206, B_205, D_207, A_204, E_208]: (m1_subset_1(k1_partfun1(A_204, B_205, C_209, D_207, E_208, F_206), k1_zfmisc_1(k2_zfmisc_1(A_204, D_207))) | ~m1_subset_1(F_206, k1_zfmisc_1(k2_zfmisc_1(C_209, D_207))) | ~v1_funct_1(F_206) | ~m1_subset_1(E_208, k1_zfmisc_1(k2_zfmisc_1(A_204, B_205))) | ~v1_funct_1(E_208))), inference(cnfTransformation, [status(thm)], [f_149])).
% 56.82/45.36  tff(c_48, plain, (![A_36]: (m1_subset_1(k6_relat_1(A_36), k1_zfmisc_1(k2_zfmisc_1(A_36, A_36))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 56.82/45.36  tff(c_83, plain, (![A_36]: (m1_subset_1(k6_partfun1(A_36), k1_zfmisc_1(k2_zfmisc_1(A_36, A_36))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_48])).
% 56.82/45.36  tff(c_68, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_204])).
% 56.82/45.36  tff(c_730, plain, (![D_146, C_147, A_148, B_149]: (D_146=C_147 | ~r2_relset_1(A_148, B_149, C_147, D_146) | ~m1_subset_1(D_146, k1_zfmisc_1(k2_zfmisc_1(A_148, B_149))) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_148, B_149))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 56.82/45.36  tff(c_738, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_68, c_730])).
% 56.82/45.36  tff(c_753, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_738])).
% 56.82/45.36  tff(c_827, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_753])).
% 56.82/45.36  tff(c_1162, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1146, c_827])).
% 56.82/45.36  tff(c_1191, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_76, c_72, c_1162])).
% 56.82/45.36  tff(c_1192, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_753])).
% 56.82/45.36  tff(c_1808, plain, (![D_264, C_263, B_267, A_266, F_265, E_268]: (k1_partfun1(A_266, B_267, C_263, D_264, E_268, F_265)=k5_relat_1(E_268, F_265) | ~m1_subset_1(F_265, k1_zfmisc_1(k2_zfmisc_1(C_263, D_264))) | ~v1_funct_1(F_265) | ~m1_subset_1(E_268, k1_zfmisc_1(k2_zfmisc_1(A_266, B_267))) | ~v1_funct_1(E_268))), inference(cnfTransformation, [status(thm)], [f_159])).
% 56.82/45.36  tff(c_1814, plain, (![A_266, B_267, E_268]: (k1_partfun1(A_266, B_267, '#skF_2', '#skF_1', E_268, '#skF_4')=k5_relat_1(E_268, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_268, k1_zfmisc_1(k2_zfmisc_1(A_266, B_267))) | ~v1_funct_1(E_268))), inference(resolution, [status(thm)], [c_72, c_1808])).
% 56.82/45.36  tff(c_1884, plain, (![A_272, B_273, E_274]: (k1_partfun1(A_272, B_273, '#skF_2', '#skF_1', E_274, '#skF_4')=k5_relat_1(E_274, '#skF_4') | ~m1_subset_1(E_274, k1_zfmisc_1(k2_zfmisc_1(A_272, B_273))) | ~v1_funct_1(E_274))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1814])).
% 56.82/45.36  tff(c_1890, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_1884])).
% 56.82/45.36  tff(c_1897, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1192, c_1890])).
% 56.82/45.36  tff(c_28, plain, (![A_16, B_18]: (v2_funct_1(A_16) | k2_relat_1(B_18)!=k1_relat_1(A_16) | ~v2_funct_1(k5_relat_1(B_18, A_16)) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_88])).
% 56.82/45.36  tff(c_1907, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1897, c_28])).
% 56.82/45.36  tff(c_1925, plain, (v2_funct_1('#skF_4') | k1_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_138, c_76, c_137, c_82, c_85, c_385, c_1907])).
% 56.82/45.36  tff(c_2079, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitLeft, [status(thm)], [c_1925])).
% 56.82/45.36  tff(c_244, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_78, c_232])).
% 56.82/45.36  tff(c_18, plain, (![A_12]: (k1_relat_1(k6_relat_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_59])).
% 56.82/45.36  tff(c_88, plain, (![A_12]: (k1_relat_1(k6_partfun1(A_12))=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_18])).
% 56.82/45.36  tff(c_16, plain, (![A_9, B_11]: (r1_tarski(k1_relat_1(k5_relat_1(A_9, B_11)), k1_relat_1(A_9)) | ~v1_relat_1(B_11) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 56.82/45.36  tff(c_169, plain, (![B_70, A_71]: (r1_tarski(k1_relat_1(B_70), A_71) | ~v4_relat_1(B_70, A_71) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_37])).
% 56.82/45.36  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 56.82/45.36  tff(c_416, plain, (![B_110, A_111]: (k1_relat_1(B_110)=A_111 | ~r1_tarski(A_111, k1_relat_1(B_110)) | ~v4_relat_1(B_110, A_111) | ~v1_relat_1(B_110))), inference(resolution, [status(thm)], [c_169, c_2])).
% 56.82/45.36  tff(c_448, plain, (![A_9, B_11]: (k1_relat_1(k5_relat_1(A_9, B_11))=k1_relat_1(A_9) | ~v4_relat_1(A_9, k1_relat_1(k5_relat_1(A_9, B_11))) | ~v1_relat_1(B_11) | ~v1_relat_1(A_9))), inference(resolution, [status(thm)], [c_16, c_416])).
% 56.82/45.36  tff(c_1904, plain, (k1_relat_1(k5_relat_1('#skF_3', '#skF_4'))=k1_relat_1('#skF_3') | ~v4_relat_1('#skF_3', k1_relat_1(k6_partfun1('#skF_1'))) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1897, c_448])).
% 56.82/45.36  tff(c_1923, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_137, c_138, c_244, c_88, c_88, c_1897, c_1904])).
% 56.82/45.36  tff(c_12, plain, (![A_5]: (k9_relat_1(A_5, k1_relat_1(A_5))=k2_relat_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 56.82/45.36  tff(c_1983, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1923, c_12])).
% 56.82/45.36  tff(c_2011, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_137, c_385, c_1983])).
% 56.82/45.36  tff(c_14, plain, (![A_6, B_8]: (k10_relat_1(A_6, k1_relat_1(B_8))=k1_relat_1(k5_relat_1(A_6, B_8)) | ~v1_relat_1(B_8) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 56.82/45.36  tff(c_454, plain, (![B_112, A_113]: (k9_relat_1(B_112, k10_relat_1(B_112, A_113))=A_113 | ~r1_tarski(A_113, k2_relat_1(B_112)) | ~v1_funct_1(B_112) | ~v1_relat_1(B_112))), inference(cnfTransformation, [status(thm)], [f_71])).
% 56.82/45.36  tff(c_456, plain, (![A_113]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_113))=A_113 | ~r1_tarski(A_113, '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_385, c_454])).
% 56.82/45.36  tff(c_498, plain, (![A_116]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_116))=A_116 | ~r1_tarski(A_116, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_82, c_456])).
% 56.82/45.36  tff(c_508, plain, (![B_8]: (k9_relat_1('#skF_3', k1_relat_1(k5_relat_1('#skF_3', B_8)))=k1_relat_1(B_8) | ~r1_tarski(k1_relat_1(B_8), '#skF_2') | ~v1_relat_1(B_8) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_498])).
% 56.82/45.36  tff(c_512, plain, (![B_8]: (k9_relat_1('#skF_3', k1_relat_1(k5_relat_1('#skF_3', B_8)))=k1_relat_1(B_8) | ~r1_tarski(k1_relat_1(B_8), '#skF_2') | ~v1_relat_1(B_8))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_508])).
% 56.82/45.36  tff(c_1910, plain, (k9_relat_1('#skF_3', k1_relat_1(k6_partfun1('#skF_1')))=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1897, c_512])).
% 56.82/45.36  tff(c_1927, plain, (k9_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_88, c_1910])).
% 56.82/45.36  tff(c_2671, plain, (k1_relat_1('#skF_4')='#skF_2' | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2011, c_1927])).
% 56.82/45.36  tff(c_2672, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_2079, c_2671])).
% 56.82/45.36  tff(c_2675, plain, (~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_2672])).
% 56.82/45.36  tff(c_2679, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_138, c_245, c_2675])).
% 56.82/45.36  tff(c_2680, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_1925])).
% 56.82/45.36  tff(c_2681, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_1925])).
% 56.82/45.36  tff(c_1223, plain, (![E_216, F_214, D_215, C_217, B_213, A_212]: (v1_funct_1(k1_partfun1(A_212, B_213, C_217, D_215, E_216, F_214)) | ~m1_subset_1(F_214, k1_zfmisc_1(k2_zfmisc_1(C_217, D_215))) | ~v1_funct_1(F_214) | ~m1_subset_1(E_216, k1_zfmisc_1(k2_zfmisc_1(A_212, B_213))) | ~v1_funct_1(E_216))), inference(cnfTransformation, [status(thm)], [f_149])).
% 56.82/45.36  tff(c_1229, plain, (![A_212, B_213, E_216]: (v1_funct_1(k1_partfun1(A_212, B_213, '#skF_2', '#skF_1', E_216, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_216, k1_zfmisc_1(k2_zfmisc_1(A_212, B_213))) | ~v1_funct_1(E_216))), inference(resolution, [status(thm)], [c_72, c_1223])).
% 56.82/45.36  tff(c_1276, plain, (![A_226, B_227, E_228]: (v1_funct_1(k1_partfun1(A_226, B_227, '#skF_2', '#skF_1', E_228, '#skF_4')) | ~m1_subset_1(E_228, k1_zfmisc_1(k2_zfmisc_1(A_226, B_227))) | ~v1_funct_1(E_228))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1229])).
% 56.82/45.36  tff(c_1282, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_1276])).
% 56.82/45.36  tff(c_1289, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1192, c_1282])).
% 56.82/45.36  tff(c_20, plain, (![A_12]: (k2_relat_1(k6_relat_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_59])).
% 56.82/45.36  tff(c_87, plain, (![A_12]: (k2_relat_1(k6_partfun1(A_12))=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_20])).
% 56.82/45.36  tff(c_22, plain, (![A_13]: (v1_relat_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 56.82/45.36  tff(c_86, plain, (![A_13]: (v1_relat_1(k6_partfun1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_22])).
% 56.82/45.36  tff(c_66, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_204])).
% 56.82/45.36  tff(c_32, plain, (![A_19, B_21]: (k2_funct_1(A_19)=B_21 | k6_relat_1(k2_relat_1(A_19))!=k5_relat_1(B_21, A_19) | k2_relat_1(B_21)!=k1_relat_1(A_19) | ~v2_funct_1(A_19) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_105])).
% 56.82/45.36  tff(c_1267, plain, (![A_224, B_225]: (k2_funct_1(A_224)=B_225 | k6_partfun1(k2_relat_1(A_224))!=k5_relat_1(B_225, A_224) | k2_relat_1(B_225)!=k1_relat_1(A_224) | ~v2_funct_1(A_224) | ~v1_funct_1(B_225) | ~v1_relat_1(B_225) | ~v1_funct_1(A_224) | ~v1_relat_1(A_224))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_32])).
% 56.82/45.36  tff(c_1269, plain, (![B_225]: (k2_funct_1('#skF_3')=B_225 | k5_relat_1(B_225, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_225)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_225) | ~v1_relat_1(B_225) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_385, c_1267])).
% 56.82/45.36  tff(c_1294, plain, (![B_230]: (k2_funct_1('#skF_3')=B_230 | k5_relat_1(B_230, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_230)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_230) | ~v1_relat_1(B_230))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_82, c_66, c_1269])).
% 56.82/45.36  tff(c_1303, plain, (![A_13]: (k6_partfun1(A_13)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_13), '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(k6_partfun1(A_13))!=k1_relat_1('#skF_3') | ~v1_funct_1(k6_partfun1(A_13)))), inference(resolution, [status(thm)], [c_86, c_1294])).
% 56.82/45.36  tff(c_1330, plain, (![A_237]: (k6_partfun1(A_237)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_237), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!=A_237 | ~v1_funct_1(k6_partfun1(A_237)))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_1303])).
% 56.82/45.36  tff(c_1334, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_1289, c_1330])).
% 56.82/45.36  tff(c_1335, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_1334])).
% 56.82/45.36  tff(c_1315, plain, (![A_234, C_231, D_232, E_236, B_235, F_233]: (k1_partfun1(A_234, B_235, C_231, D_232, E_236, F_233)=k5_relat_1(E_236, F_233) | ~m1_subset_1(F_233, k1_zfmisc_1(k2_zfmisc_1(C_231, D_232))) | ~v1_funct_1(F_233) | ~m1_subset_1(E_236, k1_zfmisc_1(k2_zfmisc_1(A_234, B_235))) | ~v1_funct_1(E_236))), inference(cnfTransformation, [status(thm)], [f_159])).
% 56.82/45.36  tff(c_1321, plain, (![A_234, B_235, E_236]: (k1_partfun1(A_234, B_235, '#skF_2', '#skF_1', E_236, '#skF_4')=k5_relat_1(E_236, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_236, k1_zfmisc_1(k2_zfmisc_1(A_234, B_235))) | ~v1_funct_1(E_236))), inference(resolution, [status(thm)], [c_72, c_1315])).
% 56.82/45.36  tff(c_1336, plain, (![A_238, B_239, E_240]: (k1_partfun1(A_238, B_239, '#skF_2', '#skF_1', E_240, '#skF_4')=k5_relat_1(E_240, '#skF_4') | ~m1_subset_1(E_240, k1_zfmisc_1(k2_zfmisc_1(A_238, B_239))) | ~v1_funct_1(E_240))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1321])).
% 56.82/45.36  tff(c_1342, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_1336])).
% 56.82/45.36  tff(c_1349, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1192, c_1342])).
% 56.82/45.36  tff(c_1356, plain, (k1_relat_1(k5_relat_1('#skF_3', '#skF_4'))=k1_relat_1('#skF_3') | ~v4_relat_1('#skF_3', k1_relat_1(k6_partfun1('#skF_1'))) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1349, c_448])).
% 56.82/45.36  tff(c_1375, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_137, c_138, c_244, c_88, c_88, c_1349, c_1356])).
% 56.82/45.36  tff(c_1377, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1335, c_1375])).
% 56.82/45.36  tff(c_1379, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_1334])).
% 56.82/45.36  tff(c_1297, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_138, c_1294])).
% 56.82/45.36  tff(c_1306, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1297])).
% 56.82/45.36  tff(c_1307, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_1306])).
% 56.82/45.36  tff(c_1313, plain, (k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_1307])).
% 56.82/45.36  tff(c_1382, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1379, c_1313])).
% 56.82/45.36  tff(c_74, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 56.82/45.36  tff(c_80, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_204])).
% 56.82/45.36  tff(c_284, plain, (![A_92, B_93, D_94]: (r2_relset_1(A_92, B_93, D_94, D_94) | ~m1_subset_1(D_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 56.82/45.36  tff(c_291, plain, (![A_36]: (r2_relset_1(A_36, A_36, k6_partfun1(A_36), k6_partfun1(A_36)))), inference(resolution, [status(thm)], [c_83, c_284])).
% 56.82/45.36  tff(c_386, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_372])).
% 56.82/45.36  tff(c_1711, plain, (![A_257, B_258, C_259, D_260]: (k2_relset_1(A_257, B_258, C_259)=B_258 | ~r2_relset_1(B_258, B_258, k1_partfun1(B_258, A_257, A_257, B_258, D_260, C_259), k6_partfun1(B_258)) | ~m1_subset_1(D_260, k1_zfmisc_1(k2_zfmisc_1(B_258, A_257))) | ~v1_funct_2(D_260, B_258, A_257) | ~v1_funct_1(D_260) | ~m1_subset_1(C_259, k1_zfmisc_1(k2_zfmisc_1(A_257, B_258))) | ~v1_funct_2(C_259, A_257, B_258) | ~v1_funct_1(C_259))), inference(cnfTransformation, [status(thm)], [f_178])).
% 56.82/45.36  tff(c_1714, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1192, c_1711])).
% 56.82/45.36  tff(c_1716, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_82, c_80, c_78, c_291, c_386, c_1714])).
% 56.82/45.36  tff(c_1718, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1382, c_1716])).
% 56.82/45.36  tff(c_1720, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_1307])).
% 56.82/45.36  tff(c_1943, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1923, c_1720])).
% 56.82/45.36  tff(c_84, plain, (![A_19, B_21]: (k2_funct_1(A_19)=B_21 | k6_partfun1(k2_relat_1(A_19))!=k5_relat_1(B_21, A_19) | k2_relat_1(B_21)!=k1_relat_1(A_19) | ~v2_funct_1(A_19) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_32])).
% 56.82/45.36  tff(c_2015, plain, (![B_21]: (k2_funct_1('#skF_4')=B_21 | k5_relat_1(B_21, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_21)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_21) | ~v1_relat_1(B_21) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1943, c_84])).
% 56.82/45.36  tff(c_2024, plain, (![B_21]: (k2_funct_1('#skF_4')=B_21 | k5_relat_1(B_21, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_21)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_21) | ~v1_relat_1(B_21))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_76, c_2015])).
% 56.82/45.36  tff(c_67393, plain, (![B_1616]: (k2_funct_1('#skF_4')=B_1616 | k5_relat_1(B_1616, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_1616)!='#skF_2' | ~v1_funct_1(B_1616) | ~v1_relat_1(B_1616))), inference(demodulation, [status(thm), theory('equality')], [c_2680, c_2681, c_2024])).
% 56.82/45.36  tff(c_67939, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_137, c_67393])).
% 56.82/45.36  tff(c_68372, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_385, c_1897, c_67939])).
% 56.82/45.36  tff(c_34, plain, (![A_22]: (k2_funct_1(k2_funct_1(A_22))=A_22 | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_113])).
% 56.82/45.36  tff(c_68379, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_68372, c_34])).
% 56.82/45.36  tff(c_68383, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_138, c_76, c_2680, c_68379])).
% 56.82/45.36  tff(c_68385, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_68383])).
% 56.82/45.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 56.82/45.36  
% 56.82/45.36  Inference rules
% 56.82/45.36  ----------------------
% 56.82/45.36  #Ref     : 0
% 56.82/45.36  #Sup     : 14151
% 56.82/45.36  #Fact    : 0
% 56.82/45.36  #Define  : 0
% 56.82/45.36  #Split   : 44
% 56.82/45.36  #Chain   : 0
% 56.82/45.36  #Close   : 0
% 56.82/45.36  
% 56.82/45.36  Ordering : KBO
% 56.82/45.36  
% 56.82/45.36  Simplification rules
% 56.82/45.36  ----------------------
% 56.82/45.36  #Subsume      : 996
% 56.82/45.36  #Demod        : 41277
% 56.82/45.36  #Tautology    : 1921
% 56.82/45.36  #SimpNegUnit  : 13
% 56.82/45.36  #BackRed      : 122
% 56.82/45.36  
% 56.82/45.36  #Partial instantiations: 0
% 56.82/45.36  #Strategies tried      : 1
% 56.82/45.36  
% 56.82/45.36  Timing (in seconds)
% 56.82/45.36  ----------------------
% 56.82/45.36  Preprocessing        : 0.36
% 56.82/45.36  Parsing              : 0.19
% 56.82/45.36  CNF conversion       : 0.03
% 56.82/45.37  Main loop            : 44.19
% 56.82/45.37  Inferencing          : 5.41
% 56.82/45.37  Reduction            : 27.64
% 56.82/45.37  Demodulation         : 25.23
% 56.82/45.37  BG Simplification    : 0.34
% 56.82/45.37  Subsumption          : 9.47
% 56.82/45.37  Abstraction          : 0.65
% 56.82/45.37  MUC search           : 0.00
% 56.82/45.37  Cooper               : 0.00
% 56.82/45.37  Total                : 44.61
% 56.82/45.37  Index Insertion      : 0.00
% 56.82/45.37  Index Deletion       : 0.00
% 56.82/45.37  Index Matching       : 0.00
% 56.82/45.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
