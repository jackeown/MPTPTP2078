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
% DateTime   : Thu Dec  3 10:13:16 EST 2020

% Result     : Theorem 13.51s
% Output     : CNFRefutation 13.57s
% Verified   : 
% Statistics : Number of formulae       :  246 (14284 expanded)
%              Number of leaves         :   48 (5060 expanded)
%              Depth                    :   31
%              Number of atoms          :  650 (65645 expanded)
%              Number of equality atoms :  206 (22985 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_262,negated_conjecture,(
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

tff(f_226,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_155,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_167,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_143,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_141,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_165,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_133,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_184,axiom,(
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

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_210,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
              & k2_relset_1(A,B,D) = B )
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | ( v2_funct_1(D)
                & v2_funct_1(E) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

tff(f_94,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_236,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_44,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_104,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_129,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

tff(f_127,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & v2_funct_1(B) )
           => k2_funct_1(k5_relat_1(A,B)) = k5_relat_1(k2_funct_1(B),k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_funct_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ! [D] :
              ( v1_relat_1(D)
             => ( ( r1_tarski(k2_relat_1(B),A)
                  & k5_relat_1(B,C) = k6_relat_1(k1_relat_1(D))
                  & k5_relat_1(C,D) = k6_relat_1(A) )
               => D = B ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_relat_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_84,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_104,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_102,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_92,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_88,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_100,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_1856,plain,(
    ! [B_193,C_194,A_195] :
      ( k6_partfun1(B_193) = k5_relat_1(k2_funct_1(C_194),C_194)
      | k1_xboole_0 = B_193
      | ~ v2_funct_1(C_194)
      | k2_relset_1(A_195,B_193,C_194) != B_193
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(A_195,B_193)))
      | ~ v1_funct_2(C_194,A_195,B_193)
      | ~ v1_funct_1(C_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_1866,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_1856])).

tff(c_1881,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_92,c_88,c_1866])).

tff(c_1882,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1881])).

tff(c_10,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_177,plain,(
    ! [B_78,A_79] :
      ( v1_relat_1(B_78)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_79))
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_186,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_100,c_177])).

tff(c_195,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_186])).

tff(c_98,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_94,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_1495,plain,(
    ! [D_155,B_156,F_152,C_153,E_154,A_151] :
      ( m1_subset_1(k1_partfun1(A_151,B_156,C_153,D_155,E_154,F_152),k1_zfmisc_1(k2_zfmisc_1(A_151,D_155)))
      | ~ m1_subset_1(F_152,k1_zfmisc_1(k2_zfmisc_1(C_153,D_155)))
      | ~ v1_funct_1(F_152)
      | ~ m1_subset_1(E_154,k1_zfmisc_1(k2_zfmisc_1(A_151,B_156)))
      | ~ v1_funct_1(E_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_60,plain,(
    ! [A_47] : k6_relat_1(A_47) = k6_partfun1(A_47) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_52,plain,(
    ! [A_34] : m1_subset_1(k6_relat_1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_105,plain,(
    ! [A_34] : m1_subset_1(k6_partfun1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_52])).

tff(c_90,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_538,plain,(
    ! [D_101,C_102,A_103,B_104] :
      ( D_101 = C_102
      | ~ r2_relset_1(A_103,B_104,C_102,D_101)
      | ~ m1_subset_1(D_101,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104)))
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_550,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_90,c_538])).

tff(c_571,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_550])).

tff(c_688,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_571])).

tff(c_1512,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1495,c_688])).

tff(c_1530,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_100,c_98,c_94,c_1512])).

tff(c_1531,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_571])).

tff(c_1782,plain,(
    ! [C_184,A_183,D_185,E_182,B_187,F_186] :
      ( k1_partfun1(A_183,B_187,C_184,D_185,E_182,F_186) = k5_relat_1(E_182,F_186)
      | ~ m1_subset_1(F_186,k1_zfmisc_1(k2_zfmisc_1(C_184,D_185)))
      | ~ v1_funct_1(F_186)
      | ~ m1_subset_1(E_182,k1_zfmisc_1(k2_zfmisc_1(A_183,B_187)))
      | ~ v1_funct_1(E_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_1790,plain,(
    ! [A_183,B_187,E_182] :
      ( k1_partfun1(A_183,B_187,'#skF_2','#skF_1',E_182,'#skF_4') = k5_relat_1(E_182,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_182,k1_zfmisc_1(k2_zfmisc_1(A_183,B_187)))
      | ~ v1_funct_1(E_182) ) ),
    inference(resolution,[status(thm)],[c_94,c_1782])).

tff(c_1805,plain,(
    ! [A_189,B_190,E_191] :
      ( k1_partfun1(A_189,B_190,'#skF_2','#skF_1',E_191,'#skF_4') = k5_relat_1(E_191,'#skF_4')
      | ~ m1_subset_1(E_191,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190)))
      | ~ v1_funct_1(E_191) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_1790])).

tff(c_1820,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_1805])).

tff(c_1831,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_1531,c_1820])).

tff(c_296,plain,(
    ! [A_90,B_91,C_92] :
      ( k2_relset_1(A_90,B_91,C_92) = k2_relat_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_305,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_296])).

tff(c_310,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_305])).

tff(c_183,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_94,c_177])).

tff(c_192,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_183])).

tff(c_20,plain,(
    ! [A_17] :
      ( v1_relat_1(k2_funct_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_86,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_96,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_308,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_94,c_296])).

tff(c_1864,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_94,c_1856])).

tff(c_1877,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_308,c_1864])).

tff(c_1878,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1877])).

tff(c_1892,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1878])).

tff(c_265,plain,(
    ! [A_85,B_86,D_87] :
      ( r2_relset_1(A_85,B_86,D_87,D_87)
      | ~ m1_subset_1(D_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_272,plain,(
    ! [A_34] : r2_relset_1(A_34,A_34,k6_partfun1(A_34),k6_partfun1(A_34)) ),
    inference(resolution,[status(thm)],[c_105,c_265])).

tff(c_2647,plain,(
    ! [A_231,B_232,C_233,D_234] :
      ( k2_relset_1(A_231,B_232,C_233) = B_232
      | ~ r2_relset_1(B_232,B_232,k1_partfun1(B_232,A_231,A_231,B_232,D_234,C_233),k6_partfun1(B_232))
      | ~ m1_subset_1(D_234,k1_zfmisc_1(k2_zfmisc_1(B_232,A_231)))
      | ~ v1_funct_2(D_234,B_232,A_231)
      | ~ v1_funct_1(D_234)
      | ~ m1_subset_1(C_233,k1_zfmisc_1(k2_zfmisc_1(A_231,B_232)))
      | ~ v1_funct_2(C_233,A_231,B_232)
      | ~ v1_funct_1(C_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_2653,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1531,c_2647])).

tff(c_2657,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_94,c_104,c_102,c_100,c_272,c_308,c_2653])).

tff(c_2659,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1892,c_2657])).

tff(c_2660,plain,
    ( ~ v2_funct_1('#skF_4')
    | k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1878])).

tff(c_2701,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2660])).

tff(c_24,plain,(
    ! [A_18] : v2_funct_1(k6_relat_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_107,plain,(
    ! [A_18] : v2_funct_1(k6_partfun1(A_18)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_24])).

tff(c_3288,plain,(
    ! [B_261,D_260,C_258,A_259,E_257] :
      ( k1_xboole_0 = C_258
      | v2_funct_1(E_257)
      | k2_relset_1(A_259,B_261,D_260) != B_261
      | ~ v2_funct_1(k1_partfun1(A_259,B_261,B_261,C_258,D_260,E_257))
      | ~ m1_subset_1(E_257,k1_zfmisc_1(k2_zfmisc_1(B_261,C_258)))
      | ~ v1_funct_2(E_257,B_261,C_258)
      | ~ v1_funct_1(E_257)
      | ~ m1_subset_1(D_260,k1_zfmisc_1(k2_zfmisc_1(A_259,B_261)))
      | ~ v1_funct_2(D_260,A_259,B_261)
      | ~ v1_funct_1(D_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_3290,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1531,c_3288])).

tff(c_3292,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_100,c_98,c_96,c_94,c_107,c_92,c_3290])).

tff(c_3294,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2701,c_86,c_3292])).

tff(c_3296,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2660])).

tff(c_2661,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1878])).

tff(c_245,plain,(
    ! [A_84] :
      ( k1_relat_1(k2_funct_1(A_84)) = k2_relat_1(A_84)
      | ~ v2_funct_1(A_84)
      | ~ v1_funct_1(A_84)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_78,plain,(
    ! [A_62] :
      ( v1_funct_2(A_62,k1_relat_1(A_62),k2_relat_1(A_62))
      | ~ v1_funct_1(A_62)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_4442,plain,(
    ! [A_300] :
      ( v1_funct_2(k2_funct_1(A_300),k2_relat_1(A_300),k2_relat_1(k2_funct_1(A_300)))
      | ~ v1_funct_1(k2_funct_1(A_300))
      | ~ v1_relat_1(k2_funct_1(A_300))
      | ~ v2_funct_1(A_300)
      | ~ v1_funct_1(A_300)
      | ~ v1_relat_1(A_300) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_78])).

tff(c_4445,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_1',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2661,c_4442])).

tff(c_4489,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_1',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_98,c_3296,c_4445])).

tff(c_4498,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_4489])).

tff(c_4502,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_4498])).

tff(c_4506,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_98,c_4502])).

tff(c_4508,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4489])).

tff(c_12,plain,(
    ! [A_8] : k1_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_111,plain,(
    ! [A_8] : k1_relat_1(k6_partfun1(A_8)) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_12])).

tff(c_18,plain,(
    ! [A_17] :
      ( v1_funct_1(k2_funct_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4507,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_4'))
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_1',k2_relat_1(k2_funct_1('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_4489])).

tff(c_4509,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_4507])).

tff(c_4512,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_4509])).

tff(c_4516,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_98,c_4512])).

tff(c_4518,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4507])).

tff(c_26,plain,(
    ! [A_19] :
      ( v2_funct_1(k2_funct_1(A_19))
      | ~ v2_funct_1(A_19)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_14,plain,(
    ! [A_8] : k2_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_110,plain,(
    ! [A_8] : k2_relat_1(k6_partfun1(A_8)) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_14])).

tff(c_2662,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2661,c_308])).

tff(c_3402,plain,(
    ! [A_265,C_266,B_267] :
      ( k6_partfun1(A_265) = k5_relat_1(C_266,k2_funct_1(C_266))
      | k1_xboole_0 = B_267
      | ~ v2_funct_1(C_266)
      | k2_relset_1(A_265,B_267,C_266) != B_267
      | ~ m1_subset_1(C_266,k1_zfmisc_1(k2_zfmisc_1(A_265,B_267)))
      | ~ v1_funct_2(C_266,A_265,B_267)
      | ~ v1_funct_1(C_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_3412,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_94,c_3402])).

tff(c_3429,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_2662,c_3296,c_3412])).

tff(c_3430,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_3429])).

tff(c_36,plain,(
    ! [A_21] :
      ( k2_relat_1(k5_relat_1(A_21,k2_funct_1(A_21))) = k1_relat_1(A_21)
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3440,plain,
    ( k2_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3430,c_36])).

tff(c_3449,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_98,c_3296,c_110,c_3440])).

tff(c_32,plain,(
    ! [A_20] :
      ( k2_relat_1(k2_funct_1(A_20)) = k1_relat_1(A_20)
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_34,plain,(
    ! [A_20] :
      ( k1_relat_1(k2_funct_1(A_20)) = k2_relat_1(A_20)
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_333,plain,(
    ! [A_94] :
      ( m1_subset_1(A_94,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_94),k2_relat_1(A_94))))
      | ~ v1_funct_1(A_94)
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_4852,plain,(
    ! [A_312] :
      ( m1_subset_1(k2_funct_1(A_312),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_312),k2_relat_1(k2_funct_1(A_312)))))
      | ~ v1_funct_1(k2_funct_1(A_312))
      | ~ v1_relat_1(k2_funct_1(A_312))
      | ~ v2_funct_1(A_312)
      | ~ v1_funct_1(A_312)
      | ~ v1_relat_1(A_312) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_333])).

tff(c_4885,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1',k2_relat_1(k2_funct_1('#skF_4')))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2661,c_4852])).

tff(c_4943,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1',k2_relat_1(k2_funct_1('#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_98,c_3296,c_4508,c_4518,c_4885])).

tff(c_4984,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1',k1_relat_1('#skF_4'))))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_4943])).

tff(c_5018,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_98,c_3296,c_3449,c_4984])).

tff(c_46,plain,(
    ! [A_27,B_28,C_29] :
      ( k2_relset_1(A_27,B_28,C_29) = k2_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_5078,plain,(
    k2_relset_1('#skF_1','#skF_2',k2_funct_1('#skF_4')) = k2_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_5018,c_46])).

tff(c_4517,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_1',k2_relat_1(k2_funct_1('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_4507])).

tff(c_4577,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_1',k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_4517])).

tff(c_4579,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_98,c_3296,c_3449,c_4577])).

tff(c_74,plain,(
    ! [A_59,C_61,B_60] :
      ( k6_partfun1(A_59) = k5_relat_1(C_61,k2_funct_1(C_61))
      | k1_xboole_0 = B_60
      | ~ v2_funct_1(C_61)
      | k2_relset_1(A_59,B_60,C_61) != B_60
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60)))
      | ~ v1_funct_2(C_61,A_59,B_60)
      | ~ v1_funct_1(C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_5022,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),k2_funct_1(k2_funct_1('#skF_4'))) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_1','#skF_2',k2_funct_1('#skF_4')) != '#skF_2'
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_1','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_5018,c_74])).

tff(c_5054,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),k2_funct_1(k2_funct_1('#skF_4'))) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_1','#skF_2',k2_funct_1('#skF_4')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4518,c_4579,c_5022])).

tff(c_5055,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),k2_funct_1(k2_funct_1('#skF_4'))) = k6_partfun1('#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_1','#skF_2',k2_funct_1('#skF_4')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_5054])).

tff(c_5089,plain,(
    k2_relset_1('#skF_1','#skF_2',k2_funct_1('#skF_4')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_5055])).

tff(c_5090,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5078,c_5089])).

tff(c_5097,plain,
    ( k1_relat_1('#skF_4') != '#skF_2'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_5090])).

tff(c_5100,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_98,c_3296,c_3449,c_5097])).

tff(c_5102,plain,(
    k2_relset_1('#skF_1','#skF_2',k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5055])).

tff(c_72,plain,(
    ! [B_60,C_61,A_59] :
      ( k6_partfun1(B_60) = k5_relat_1(k2_funct_1(C_61),C_61)
      | k1_xboole_0 = B_60
      | ~ v2_funct_1(C_61)
      | k2_relset_1(A_59,B_60,C_61) != B_60
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60)))
      | ~ v1_funct_2(C_61,A_59,B_60)
      | ~ v1_funct_1(C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_5027,plain,
    ( k5_relat_1(k2_funct_1(k2_funct_1('#skF_4')),k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_1','#skF_2',k2_funct_1('#skF_4')) != '#skF_2'
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_1','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_5018,c_72])).

tff(c_5061,plain,
    ( k5_relat_1(k2_funct_1(k2_funct_1('#skF_4')),k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_1','#skF_2',k2_funct_1('#skF_4')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4518,c_4579,c_5027])).

tff(c_5062,plain,
    ( k5_relat_1(k2_funct_1(k2_funct_1('#skF_4')),k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_1','#skF_2',k2_funct_1('#skF_4')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_5061])).

tff(c_5377,plain,
    ( k5_relat_1(k2_funct_1(k2_funct_1('#skF_4')),k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5102,c_5062])).

tff(c_5378,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_5377])).

tff(c_5381,plain,
    ( ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_5378])).

tff(c_5385,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_98,c_3296,c_5381])).

tff(c_5387,plain,(
    v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_5377])).

tff(c_44,plain,(
    ! [A_26] : k2_funct_1(k6_relat_1(A_26)) = k6_relat_1(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_106,plain,(
    ! [A_26] : k2_funct_1(k6_partfun1(A_26)) = k6_partfun1(A_26) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_60,c_44])).

tff(c_3295,plain,(
    k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2660])).

tff(c_275,plain,(
    ! [A_88] :
      ( k2_relat_1(k2_funct_1(A_88)) = k1_relat_1(A_88)
      | ~ v2_funct_1(A_88)
      | ~ v1_funct_1(A_88)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_4519,plain,(
    ! [A_301] :
      ( v1_funct_2(k2_funct_1(A_301),k1_relat_1(k2_funct_1(A_301)),k1_relat_1(A_301))
      | ~ v1_funct_1(k2_funct_1(A_301))
      | ~ v1_relat_1(k2_funct_1(A_301))
      | ~ v2_funct_1(A_301)
      | ~ v1_funct_1(A_301)
      | ~ v1_relat_1(A_301) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_78])).

tff(c_4525,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3449,c_4519])).

tff(c_4568,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_98,c_3296,c_4508,c_4518,c_4525])).

tff(c_5107,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5102,c_5078])).

tff(c_357,plain,(
    ! [A_94] :
      ( k2_relset_1(k1_relat_1(A_94),k2_relat_1(A_94),A_94) = k2_relat_1(A_94)
      | ~ v1_funct_1(A_94)
      | ~ v1_relat_1(A_94) ) ),
    inference(resolution,[status(thm)],[c_333,c_46])).

tff(c_5133,plain,
    ( k2_relset_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_2',k2_funct_1('#skF_4')) = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5107,c_357])).

tff(c_5164,plain,(
    k2_relset_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_2',k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4508,c_4518,c_5107,c_5133])).

tff(c_5421,plain,(
    ! [A_317] :
      ( m1_subset_1(k2_funct_1(A_317),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_317)),k1_relat_1(A_317))))
      | ~ v1_funct_1(k2_funct_1(A_317))
      | ~ v1_relat_1(k2_funct_1(A_317))
      | ~ v2_funct_1(A_317)
      | ~ v1_funct_1(A_317)
      | ~ v1_relat_1(A_317) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_333])).

tff(c_5457,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_2')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3449,c_5421])).

tff(c_5514,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_98,c_3296,c_4508,c_4518,c_5457])).

tff(c_5594,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),k2_funct_1(k2_funct_1('#skF_4'))) = k6_partfun1(k1_relat_1(k2_funct_1('#skF_4')))
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_2',k2_funct_1('#skF_4')) != '#skF_2'
    | ~ v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_5514,c_74])).

tff(c_5629,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),k2_funct_1(k2_funct_1('#skF_4'))) = k6_partfun1(k1_relat_1(k2_funct_1('#skF_4')))
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4518,c_4568,c_5164,c_5387,c_5594])).

tff(c_5630,plain,(
    k5_relat_1(k2_funct_1('#skF_4'),k2_funct_1(k2_funct_1('#skF_4'))) = k6_partfun1(k1_relat_1(k2_funct_1('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_5629])).

tff(c_42,plain,(
    ! [B_25,A_23] :
      ( k5_relat_1(k2_funct_1(B_25),k2_funct_1(A_23)) = k2_funct_1(k5_relat_1(A_23,B_25))
      | ~ v2_funct_1(B_25)
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_5666,plain,
    ( k6_partfun1(k1_relat_1(k2_funct_1('#skF_4'))) = k2_funct_1(k5_relat_1(k2_funct_1('#skF_4'),'#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5630,c_42])).

tff(c_5684,plain,(
    k6_partfun1(k1_relat_1(k2_funct_1('#skF_4'))) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4508,c_4518,c_192,c_98,c_5387,c_3296,c_106,c_3295,c_5666])).

tff(c_5777,plain,(
    k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5684,c_111])).

tff(c_5833,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_5777])).

tff(c_16,plain,(
    ! [D_16,B_10,A_9,C_14] :
      ( D_16 = B_10
      | k6_relat_1(A_9) != k5_relat_1(C_14,D_16)
      | k6_relat_1(k1_relat_1(D_16)) != k5_relat_1(B_10,C_14)
      | ~ r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v1_relat_1(D_16)
      | ~ v1_relat_1(C_14)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_109,plain,(
    ! [D_16,B_10,A_9,C_14] :
      ( D_16 = B_10
      | k6_partfun1(A_9) != k5_relat_1(C_14,D_16)
      | k6_partfun1(k1_relat_1(D_16)) != k5_relat_1(B_10,C_14)
      | ~ r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v1_relat_1(D_16)
      | ~ v1_relat_1(C_14)
      | ~ v1_relat_1(B_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_60,c_16])).

tff(c_3437,plain,(
    ! [B_10,A_9] :
      ( k2_funct_1('#skF_4') = B_10
      | k6_partfun1(A_9) != k6_partfun1('#skF_2')
      | k6_partfun1(k1_relat_1(k2_funct_1('#skF_4'))) != k5_relat_1(B_10,'#skF_4')
      | ~ r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v1_relat_1(k2_funct_1('#skF_4'))
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(B_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3430,c_109])).

tff(c_3447,plain,(
    ! [B_10,A_9] :
      ( k2_funct_1('#skF_4') = B_10
      | k6_partfun1(A_9) != k6_partfun1('#skF_2')
      | k6_partfun1(k1_relat_1(k2_funct_1('#skF_4'))) != k5_relat_1(B_10,'#skF_4')
      | ~ r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v1_relat_1(k2_funct_1('#skF_4'))
      | ~ v1_relat_1(B_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_3437])).

tff(c_15385,plain,(
    ! [B_468,A_469] :
      ( k2_funct_1('#skF_4') = B_468
      | k6_partfun1(A_469) != k6_partfun1('#skF_2')
      | k5_relat_1(B_468,'#skF_4') != k6_partfun1('#skF_1')
      | ~ r1_tarski(k2_relat_1(B_468),A_469)
      | ~ v1_relat_1(B_468) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4508,c_5833,c_3447])).

tff(c_15415,plain,(
    ! [A_469] :
      ( k2_funct_1('#skF_4') = '#skF_3'
      | k6_partfun1(A_469) != k6_partfun1('#skF_2')
      | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
      | ~ r1_tarski('#skF_2',A_469)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_15385])).

tff(c_15434,plain,(
    ! [A_469] :
      ( k2_funct_1('#skF_4') = '#skF_3'
      | k6_partfun1(A_469) != k6_partfun1('#skF_2')
      | ~ r1_tarski('#skF_2',A_469) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_1831,c_15415])).

tff(c_15676,plain,(
    ! [A_470] :
      ( k6_partfun1(A_470) != k6_partfun1('#skF_2')
      | ~ r1_tarski('#skF_2',A_470) ) ),
    inference(splitLeft,[status(thm)],[c_15434])).

tff(c_15682,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_15676])).

tff(c_15683,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_15434])).

tff(c_82,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_4466,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_4442])).

tff(c_4491,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_104,c_88,c_4466])).

tff(c_4586,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_4491])).

tff(c_4589,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_4586])).

tff(c_4593,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_104,c_4589])).

tff(c_4595,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_4491])).

tff(c_3414,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_3402])).

tff(c_3433,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_92,c_88,c_3414])).

tff(c_3434,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_3433])).

tff(c_3505,plain,
    ( k2_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3434,c_36])).

tff(c_3514,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_104,c_88,c_110,c_3505])).

tff(c_4594,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_3'))
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_4491])).

tff(c_4596,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_4594])).

tff(c_4664,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_4596])).

tff(c_4668,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_104,c_4664])).

tff(c_4670,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_4594])).

tff(c_4906,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3')))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_4852])).

tff(c_4945,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_104,c_88,c_4595,c_4670,c_4906])).

tff(c_5277,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3'))))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_4945])).

tff(c_5311,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_104,c_88,c_3514,c_5277])).

tff(c_5371,plain,(
    k2_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_5311,c_46])).

tff(c_4669,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_4594])).

tff(c_4673,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_4669])).

tff(c_4675,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_104,c_88,c_3514,c_4673])).

tff(c_5320,plain,
    ( k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_1'
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_5311,c_72])).

tff(c_5354,plain,
    ( k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4670,c_4675,c_5320])).

tff(c_5355,plain,
    ( k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_5354])).

tff(c_5978,plain,
    ( k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relat_1(k2_funct_1('#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5371,c_5355])).

tff(c_5979,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_5978])).

tff(c_5982,plain,
    ( k1_relat_1('#skF_3') != '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_5979])).

tff(c_5985,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_104,c_88,c_3514,c_5982])).

tff(c_5987,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5978])).

tff(c_3299,plain,(
    ! [B_10,A_9] :
      ( B_10 = '#skF_4'
      | k6_partfun1(A_9) != k6_partfun1('#skF_1')
      | k5_relat_1(B_10,k2_funct_1('#skF_4')) != k6_partfun1(k1_relat_1('#skF_4'))
      | ~ r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(k2_funct_1('#skF_4'))
      | ~ v1_relat_1(B_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3295,c_109])).

tff(c_3303,plain,(
    ! [B_10,A_9] :
      ( B_10 = '#skF_4'
      | k6_partfun1(A_9) != k6_partfun1('#skF_1')
      | k5_relat_1(B_10,k2_funct_1('#skF_4')) != k6_partfun1(k1_relat_1('#skF_4'))
      | ~ r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v1_relat_1(k2_funct_1('#skF_4'))
      | ~ v1_relat_1(B_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_3299])).

tff(c_14641,plain,(
    ! [B_463,A_464] :
      ( B_463 = '#skF_4'
      | k6_partfun1(A_464) != k6_partfun1('#skF_1')
      | k5_relat_1(B_463,k2_funct_1('#skF_4')) != k6_partfun1('#skF_2')
      | ~ r1_tarski(k2_relat_1(B_463),A_464)
      | ~ v1_relat_1(B_463) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4508,c_3449,c_3303])).

tff(c_14653,plain,(
    ! [A_464] :
      ( k2_funct_1('#skF_3') = '#skF_4'
      | k6_partfun1(A_464) != k6_partfun1('#skF_1')
      | k5_relat_1(k2_funct_1('#skF_3'),k2_funct_1('#skF_4')) != k6_partfun1('#skF_2')
      | ~ r1_tarski('#skF_1',A_464)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5987,c_14641])).

tff(c_14683,plain,(
    ! [A_464] :
      ( k2_funct_1('#skF_3') = '#skF_4'
      | k6_partfun1(A_464) != k6_partfun1('#skF_1')
      | k5_relat_1(k2_funct_1('#skF_3'),k2_funct_1('#skF_4')) != k6_partfun1('#skF_2')
      | ~ r1_tarski('#skF_1',A_464) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4595,c_14653])).

tff(c_14684,plain,(
    ! [A_464] :
      ( k6_partfun1(A_464) != k6_partfun1('#skF_1')
      | k5_relat_1(k2_funct_1('#skF_3'),k2_funct_1('#skF_4')) != k6_partfun1('#skF_2')
      | ~ r1_tarski('#skF_1',A_464) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_14683])).

tff(c_14698,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k2_funct_1('#skF_4')) != k6_partfun1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_14684])).

tff(c_15688,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15683,c_14698])).

tff(c_15726,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1882,c_15688])).

tff(c_15729,plain,(
    ! [A_471] :
      ( k6_partfun1(A_471) != k6_partfun1('#skF_1')
      | ~ r1_tarski('#skF_1',A_471) ) ),
    inference(splitRight,[status(thm)],[c_14684])).

tff(c_15735,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_15729])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:41:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.51/5.92  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.57/5.95  
% 13.57/5.95  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.57/5.96  %$ r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 13.57/5.96  
% 13.57/5.96  %Foreground sorts:
% 13.57/5.96  
% 13.57/5.96  
% 13.57/5.96  %Background operators:
% 13.57/5.96  
% 13.57/5.96  
% 13.57/5.96  %Foreground operators:
% 13.57/5.96  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 13.57/5.96  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.57/5.96  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 13.57/5.96  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 13.57/5.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.57/5.96  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 13.57/5.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.57/5.96  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 13.57/5.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.57/5.96  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.57/5.96  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.57/5.96  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.57/5.96  tff('#skF_2', type, '#skF_2': $i).
% 13.57/5.96  tff('#skF_3', type, '#skF_3': $i).
% 13.57/5.96  tff('#skF_1', type, '#skF_1': $i).
% 13.57/5.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.57/5.96  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 13.57/5.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.57/5.96  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.57/5.96  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.57/5.96  tff('#skF_4', type, '#skF_4': $i).
% 13.57/5.96  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 13.57/5.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.57/5.96  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.57/5.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.57/5.96  
% 13.57/5.99  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.57/5.99  tff(f_262, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 13.57/5.99  tff(f_226, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 13.57/5.99  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 13.57/5.99  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 13.57/5.99  tff(f_155, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 13.57/5.99  tff(f_167, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 13.57/5.99  tff(f_143, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 13.57/5.99  tff(f_141, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 13.57/5.99  tff(f_165, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 13.57/5.99  tff(f_133, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 13.57/5.99  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 13.57/5.99  tff(f_184, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 13.57/5.99  tff(f_72, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 13.57/5.99  tff(f_210, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 13.57/5.99  tff(f_94, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 13.57/5.99  tff(f_236, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 13.57/5.99  tff(f_44, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 13.57/5.99  tff(f_84, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 13.57/5.99  tff(f_104, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_funct_1)).
% 13.57/5.99  tff(f_129, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_1)).
% 13.57/5.99  tff(f_127, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(A) & v2_funct_1(B)) => (k2_funct_1(k5_relat_1(A, B)) = k5_relat_1(k2_funct_1(B), k2_funct_1(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_funct_1)).
% 13.57/5.99  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => (((r1_tarski(k2_relat_1(B), A) & (k5_relat_1(B, C) = k6_relat_1(k1_relat_1(D)))) & (k5_relat_1(C, D) = k6_relat_1(A))) => (D = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_relat_1)).
% 13.57/5.99  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.57/5.99  tff(c_84, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_262])).
% 13.57/5.99  tff(c_104, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_262])).
% 13.57/5.99  tff(c_102, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_262])).
% 13.57/5.99  tff(c_92, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_262])).
% 13.57/5.99  tff(c_88, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_262])).
% 13.57/5.99  tff(c_100, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_262])).
% 13.57/5.99  tff(c_1856, plain, (![B_193, C_194, A_195]: (k6_partfun1(B_193)=k5_relat_1(k2_funct_1(C_194), C_194) | k1_xboole_0=B_193 | ~v2_funct_1(C_194) | k2_relset_1(A_195, B_193, C_194)!=B_193 | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(A_195, B_193))) | ~v1_funct_2(C_194, A_195, B_193) | ~v1_funct_1(C_194))), inference(cnfTransformation, [status(thm)], [f_226])).
% 13.57/5.99  tff(c_1866, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_100, c_1856])).
% 13.57/5.99  tff(c_1881, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_92, c_88, c_1866])).
% 13.57/5.99  tff(c_1882, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_84, c_1881])).
% 13.57/5.99  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 13.57/5.99  tff(c_177, plain, (![B_78, A_79]: (v1_relat_1(B_78) | ~m1_subset_1(B_78, k1_zfmisc_1(A_79)) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.57/5.99  tff(c_186, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_100, c_177])).
% 13.57/5.99  tff(c_195, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_186])).
% 13.57/5.99  tff(c_98, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_262])).
% 13.57/5.99  tff(c_94, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_262])).
% 13.57/5.99  tff(c_1495, plain, (![D_155, B_156, F_152, C_153, E_154, A_151]: (m1_subset_1(k1_partfun1(A_151, B_156, C_153, D_155, E_154, F_152), k1_zfmisc_1(k2_zfmisc_1(A_151, D_155))) | ~m1_subset_1(F_152, k1_zfmisc_1(k2_zfmisc_1(C_153, D_155))) | ~v1_funct_1(F_152) | ~m1_subset_1(E_154, k1_zfmisc_1(k2_zfmisc_1(A_151, B_156))) | ~v1_funct_1(E_154))), inference(cnfTransformation, [status(thm)], [f_155])).
% 13.57/5.99  tff(c_60, plain, (![A_47]: (k6_relat_1(A_47)=k6_partfun1(A_47))), inference(cnfTransformation, [status(thm)], [f_167])).
% 13.57/5.99  tff(c_52, plain, (![A_34]: (m1_subset_1(k6_relat_1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 13.57/5.99  tff(c_105, plain, (![A_34]: (m1_subset_1(k6_partfun1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_52])).
% 13.57/5.99  tff(c_90, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_262])).
% 13.57/5.99  tff(c_538, plain, (![D_101, C_102, A_103, B_104]: (D_101=C_102 | ~r2_relset_1(A_103, B_104, C_102, D_101) | ~m1_subset_1(D_101, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_141])).
% 13.57/5.99  tff(c_550, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_90, c_538])).
% 13.57/5.99  tff(c_571, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_550])).
% 13.57/5.99  tff(c_688, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_571])).
% 13.57/5.99  tff(c_1512, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1495, c_688])).
% 13.57/5.99  tff(c_1530, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_100, c_98, c_94, c_1512])).
% 13.57/5.99  tff(c_1531, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_571])).
% 13.57/5.99  tff(c_1782, plain, (![C_184, A_183, D_185, E_182, B_187, F_186]: (k1_partfun1(A_183, B_187, C_184, D_185, E_182, F_186)=k5_relat_1(E_182, F_186) | ~m1_subset_1(F_186, k1_zfmisc_1(k2_zfmisc_1(C_184, D_185))) | ~v1_funct_1(F_186) | ~m1_subset_1(E_182, k1_zfmisc_1(k2_zfmisc_1(A_183, B_187))) | ~v1_funct_1(E_182))), inference(cnfTransformation, [status(thm)], [f_165])).
% 13.57/5.99  tff(c_1790, plain, (![A_183, B_187, E_182]: (k1_partfun1(A_183, B_187, '#skF_2', '#skF_1', E_182, '#skF_4')=k5_relat_1(E_182, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_182, k1_zfmisc_1(k2_zfmisc_1(A_183, B_187))) | ~v1_funct_1(E_182))), inference(resolution, [status(thm)], [c_94, c_1782])).
% 13.57/5.99  tff(c_1805, plain, (![A_189, B_190, E_191]: (k1_partfun1(A_189, B_190, '#skF_2', '#skF_1', E_191, '#skF_4')=k5_relat_1(E_191, '#skF_4') | ~m1_subset_1(E_191, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))) | ~v1_funct_1(E_191))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_1790])).
% 13.57/5.99  tff(c_1820, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_100, c_1805])).
% 13.57/5.99  tff(c_1831, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_1531, c_1820])).
% 13.57/5.99  tff(c_296, plain, (![A_90, B_91, C_92]: (k2_relset_1(A_90, B_91, C_92)=k2_relat_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 13.57/5.99  tff(c_305, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_100, c_296])).
% 13.57/5.99  tff(c_310, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_305])).
% 13.57/5.99  tff(c_183, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_94, c_177])).
% 13.57/5.99  tff(c_192, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_183])).
% 13.57/5.99  tff(c_20, plain, (![A_17]: (v1_relat_1(k2_funct_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.57/5.99  tff(c_86, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_262])).
% 13.57/5.99  tff(c_96, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_262])).
% 13.57/5.99  tff(c_308, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_94, c_296])).
% 13.57/5.99  tff(c_1864, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_94, c_1856])).
% 13.57/5.99  tff(c_1877, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_308, c_1864])).
% 13.57/5.99  tff(c_1878, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_86, c_1877])).
% 13.57/5.99  tff(c_1892, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_1878])).
% 13.57/5.99  tff(c_265, plain, (![A_85, B_86, D_87]: (r2_relset_1(A_85, B_86, D_87, D_87) | ~m1_subset_1(D_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_141])).
% 13.57/5.99  tff(c_272, plain, (![A_34]: (r2_relset_1(A_34, A_34, k6_partfun1(A_34), k6_partfun1(A_34)))), inference(resolution, [status(thm)], [c_105, c_265])).
% 13.57/5.99  tff(c_2647, plain, (![A_231, B_232, C_233, D_234]: (k2_relset_1(A_231, B_232, C_233)=B_232 | ~r2_relset_1(B_232, B_232, k1_partfun1(B_232, A_231, A_231, B_232, D_234, C_233), k6_partfun1(B_232)) | ~m1_subset_1(D_234, k1_zfmisc_1(k2_zfmisc_1(B_232, A_231))) | ~v1_funct_2(D_234, B_232, A_231) | ~v1_funct_1(D_234) | ~m1_subset_1(C_233, k1_zfmisc_1(k2_zfmisc_1(A_231, B_232))) | ~v1_funct_2(C_233, A_231, B_232) | ~v1_funct_1(C_233))), inference(cnfTransformation, [status(thm)], [f_184])).
% 13.57/5.99  tff(c_2653, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1531, c_2647])).
% 13.57/5.99  tff(c_2657, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_94, c_104, c_102, c_100, c_272, c_308, c_2653])).
% 13.57/5.99  tff(c_2659, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1892, c_2657])).
% 13.57/5.99  tff(c_2660, plain, (~v2_funct_1('#skF_4') | k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1878])).
% 13.57/5.99  tff(c_2701, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_2660])).
% 13.57/5.99  tff(c_24, plain, (![A_18]: (v2_funct_1(k6_relat_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 13.57/5.99  tff(c_107, plain, (![A_18]: (v2_funct_1(k6_partfun1(A_18)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_24])).
% 13.57/5.99  tff(c_3288, plain, (![B_261, D_260, C_258, A_259, E_257]: (k1_xboole_0=C_258 | v2_funct_1(E_257) | k2_relset_1(A_259, B_261, D_260)!=B_261 | ~v2_funct_1(k1_partfun1(A_259, B_261, B_261, C_258, D_260, E_257)) | ~m1_subset_1(E_257, k1_zfmisc_1(k2_zfmisc_1(B_261, C_258))) | ~v1_funct_2(E_257, B_261, C_258) | ~v1_funct_1(E_257) | ~m1_subset_1(D_260, k1_zfmisc_1(k2_zfmisc_1(A_259, B_261))) | ~v1_funct_2(D_260, A_259, B_261) | ~v1_funct_1(D_260))), inference(cnfTransformation, [status(thm)], [f_210])).
% 13.57/5.99  tff(c_3290, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1531, c_3288])).
% 13.57/5.99  tff(c_3292, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_100, c_98, c_96, c_94, c_107, c_92, c_3290])).
% 13.57/5.99  tff(c_3294, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2701, c_86, c_3292])).
% 13.57/5.99  tff(c_3296, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_2660])).
% 13.57/5.99  tff(c_2661, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_1878])).
% 13.57/5.99  tff(c_245, plain, (![A_84]: (k1_relat_1(k2_funct_1(A_84))=k2_relat_1(A_84) | ~v2_funct_1(A_84) | ~v1_funct_1(A_84) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.57/5.99  tff(c_78, plain, (![A_62]: (v1_funct_2(A_62, k1_relat_1(A_62), k2_relat_1(A_62)) | ~v1_funct_1(A_62) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_236])).
% 13.57/5.99  tff(c_4442, plain, (![A_300]: (v1_funct_2(k2_funct_1(A_300), k2_relat_1(A_300), k2_relat_1(k2_funct_1(A_300))) | ~v1_funct_1(k2_funct_1(A_300)) | ~v1_relat_1(k2_funct_1(A_300)) | ~v2_funct_1(A_300) | ~v1_funct_1(A_300) | ~v1_relat_1(A_300))), inference(superposition, [status(thm), theory('equality')], [c_245, c_78])).
% 13.57/5.99  tff(c_4445, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_1', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2661, c_4442])).
% 13.57/5.99  tff(c_4489, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_1', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_192, c_98, c_3296, c_4445])).
% 13.57/5.99  tff(c_4498, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_4489])).
% 13.57/5.99  tff(c_4502, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_4498])).
% 13.57/5.99  tff(c_4506, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_192, c_98, c_4502])).
% 13.57/5.99  tff(c_4508, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_4489])).
% 13.57/5.99  tff(c_12, plain, (![A_8]: (k1_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.57/5.99  tff(c_111, plain, (![A_8]: (k1_relat_1(k6_partfun1(A_8))=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_12])).
% 13.57/5.99  tff(c_18, plain, (![A_17]: (v1_funct_1(k2_funct_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.57/5.99  tff(c_4507, plain, (~v1_funct_1(k2_funct_1('#skF_4')) | v1_funct_2(k2_funct_1('#skF_4'), '#skF_1', k2_relat_1(k2_funct_1('#skF_4')))), inference(splitRight, [status(thm)], [c_4489])).
% 13.57/5.99  tff(c_4509, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_4507])).
% 13.57/5.99  tff(c_4512, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_4509])).
% 13.57/5.99  tff(c_4516, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_192, c_98, c_4512])).
% 13.57/5.99  tff(c_4518, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_4507])).
% 13.57/5.99  tff(c_26, plain, (![A_19]: (v2_funct_1(k2_funct_1(A_19)) | ~v2_funct_1(A_19) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_84])).
% 13.57/5.99  tff(c_14, plain, (![A_8]: (k2_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.57/5.99  tff(c_110, plain, (![A_8]: (k2_relat_1(k6_partfun1(A_8))=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_14])).
% 13.57/5.99  tff(c_2662, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2661, c_308])).
% 13.57/5.99  tff(c_3402, plain, (![A_265, C_266, B_267]: (k6_partfun1(A_265)=k5_relat_1(C_266, k2_funct_1(C_266)) | k1_xboole_0=B_267 | ~v2_funct_1(C_266) | k2_relset_1(A_265, B_267, C_266)!=B_267 | ~m1_subset_1(C_266, k1_zfmisc_1(k2_zfmisc_1(A_265, B_267))) | ~v1_funct_2(C_266, A_265, B_267) | ~v1_funct_1(C_266))), inference(cnfTransformation, [status(thm)], [f_226])).
% 13.57/5.99  tff(c_3412, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_94, c_3402])).
% 13.57/5.99  tff(c_3429, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_2662, c_3296, c_3412])).
% 13.57/5.99  tff(c_3430, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_86, c_3429])).
% 13.57/5.99  tff(c_36, plain, (![A_21]: (k2_relat_1(k5_relat_1(A_21, k2_funct_1(A_21)))=k1_relat_1(A_21) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_104])).
% 13.57/5.99  tff(c_3440, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3430, c_36])).
% 13.57/5.99  tff(c_3449, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_192, c_98, c_3296, c_110, c_3440])).
% 13.57/5.99  tff(c_32, plain, (![A_20]: (k2_relat_1(k2_funct_1(A_20))=k1_relat_1(A_20) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.57/5.99  tff(c_34, plain, (![A_20]: (k1_relat_1(k2_funct_1(A_20))=k2_relat_1(A_20) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.57/5.99  tff(c_333, plain, (![A_94]: (m1_subset_1(A_94, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_94), k2_relat_1(A_94)))) | ~v1_funct_1(A_94) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_236])).
% 13.57/5.99  tff(c_4852, plain, (![A_312]: (m1_subset_1(k2_funct_1(A_312), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_312), k2_relat_1(k2_funct_1(A_312))))) | ~v1_funct_1(k2_funct_1(A_312)) | ~v1_relat_1(k2_funct_1(A_312)) | ~v2_funct_1(A_312) | ~v1_funct_1(A_312) | ~v1_relat_1(A_312))), inference(superposition, [status(thm), theory('equality')], [c_34, c_333])).
% 13.57/5.99  tff(c_4885, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', k2_relat_1(k2_funct_1('#skF_4'))))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2661, c_4852])).
% 13.57/5.99  tff(c_4943, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', k2_relat_1(k2_funct_1('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_192, c_98, c_3296, c_4508, c_4518, c_4885])).
% 13.57/5.99  tff(c_4984, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', k1_relat_1('#skF_4')))) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_32, c_4943])).
% 13.57/5.99  tff(c_5018, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_192, c_98, c_3296, c_3449, c_4984])).
% 13.57/5.99  tff(c_46, plain, (![A_27, B_28, C_29]: (k2_relset_1(A_27, B_28, C_29)=k2_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 13.57/5.99  tff(c_5078, plain, (k2_relset_1('#skF_1', '#skF_2', k2_funct_1('#skF_4'))=k2_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_5018, c_46])).
% 13.57/5.99  tff(c_4517, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_1', k2_relat_1(k2_funct_1('#skF_4')))), inference(splitRight, [status(thm)], [c_4507])).
% 13.57/5.99  tff(c_4577, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_1', k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_32, c_4517])).
% 13.57/5.99  tff(c_4579, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_192, c_98, c_3296, c_3449, c_4577])).
% 13.57/5.99  tff(c_74, plain, (![A_59, C_61, B_60]: (k6_partfun1(A_59)=k5_relat_1(C_61, k2_funct_1(C_61)) | k1_xboole_0=B_60 | ~v2_funct_1(C_61) | k2_relset_1(A_59, B_60, C_61)!=B_60 | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))) | ~v1_funct_2(C_61, A_59, B_60) | ~v1_funct_1(C_61))), inference(cnfTransformation, [status(thm)], [f_226])).
% 13.57/5.99  tff(c_5022, plain, (k5_relat_1(k2_funct_1('#skF_4'), k2_funct_1(k2_funct_1('#skF_4')))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_1', '#skF_2', k2_funct_1('#skF_4'))!='#skF_2' | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_1', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_5018, c_74])).
% 13.57/5.99  tff(c_5054, plain, (k5_relat_1(k2_funct_1('#skF_4'), k2_funct_1(k2_funct_1('#skF_4')))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_1', '#skF_2', k2_funct_1('#skF_4'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4518, c_4579, c_5022])).
% 13.57/5.99  tff(c_5055, plain, (k5_relat_1(k2_funct_1('#skF_4'), k2_funct_1(k2_funct_1('#skF_4')))=k6_partfun1('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_1', '#skF_2', k2_funct_1('#skF_4'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_84, c_5054])).
% 13.57/5.99  tff(c_5089, plain, (k2_relset_1('#skF_1', '#skF_2', k2_funct_1('#skF_4'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_5055])).
% 13.57/5.99  tff(c_5090, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5078, c_5089])).
% 13.57/5.99  tff(c_5097, plain, (k1_relat_1('#skF_4')!='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_32, c_5090])).
% 13.57/5.99  tff(c_5100, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_192, c_98, c_3296, c_3449, c_5097])).
% 13.57/5.99  tff(c_5102, plain, (k2_relset_1('#skF_1', '#skF_2', k2_funct_1('#skF_4'))='#skF_2'), inference(splitRight, [status(thm)], [c_5055])).
% 13.57/5.99  tff(c_72, plain, (![B_60, C_61, A_59]: (k6_partfun1(B_60)=k5_relat_1(k2_funct_1(C_61), C_61) | k1_xboole_0=B_60 | ~v2_funct_1(C_61) | k2_relset_1(A_59, B_60, C_61)!=B_60 | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))) | ~v1_funct_2(C_61, A_59, B_60) | ~v1_funct_1(C_61))), inference(cnfTransformation, [status(thm)], [f_226])).
% 13.57/5.99  tff(c_5027, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_4')), k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_1', '#skF_2', k2_funct_1('#skF_4'))!='#skF_2' | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_1', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_5018, c_72])).
% 13.57/5.99  tff(c_5061, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_4')), k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_1', '#skF_2', k2_funct_1('#skF_4'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4518, c_4579, c_5027])).
% 13.57/5.99  tff(c_5062, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_4')), k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_1', '#skF_2', k2_funct_1('#skF_4'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_84, c_5061])).
% 13.57/5.99  tff(c_5377, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_4')), k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5102, c_5062])).
% 13.57/5.99  tff(c_5378, plain, (~v2_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_5377])).
% 13.57/5.99  tff(c_5381, plain, (~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_5378])).
% 13.57/5.99  tff(c_5385, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_192, c_98, c_3296, c_5381])).
% 13.57/5.99  tff(c_5387, plain, (v2_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_5377])).
% 13.57/5.99  tff(c_44, plain, (![A_26]: (k2_funct_1(k6_relat_1(A_26))=k6_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_129])).
% 13.57/5.99  tff(c_106, plain, (![A_26]: (k2_funct_1(k6_partfun1(A_26))=k6_partfun1(A_26))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_60, c_44])).
% 13.57/5.99  tff(c_3295, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2660])).
% 13.57/5.99  tff(c_275, plain, (![A_88]: (k2_relat_1(k2_funct_1(A_88))=k1_relat_1(A_88) | ~v2_funct_1(A_88) | ~v1_funct_1(A_88) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.57/5.99  tff(c_4519, plain, (![A_301]: (v1_funct_2(k2_funct_1(A_301), k1_relat_1(k2_funct_1(A_301)), k1_relat_1(A_301)) | ~v1_funct_1(k2_funct_1(A_301)) | ~v1_relat_1(k2_funct_1(A_301)) | ~v2_funct_1(A_301) | ~v1_funct_1(A_301) | ~v1_relat_1(A_301))), inference(superposition, [status(thm), theory('equality')], [c_275, c_78])).
% 13.57/5.99  tff(c_4525, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3449, c_4519])).
% 13.57/5.99  tff(c_4568, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_192, c_98, c_3296, c_4508, c_4518, c_4525])).
% 13.57/5.99  tff(c_5107, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5102, c_5078])).
% 13.57/5.99  tff(c_357, plain, (![A_94]: (k2_relset_1(k1_relat_1(A_94), k2_relat_1(A_94), A_94)=k2_relat_1(A_94) | ~v1_funct_1(A_94) | ~v1_relat_1(A_94))), inference(resolution, [status(thm)], [c_333, c_46])).
% 13.57/5.99  tff(c_5133, plain, (k2_relset_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_2', k2_funct_1('#skF_4'))=k2_relat_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5107, c_357])).
% 13.57/5.99  tff(c_5164, plain, (k2_relset_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_2', k2_funct_1('#skF_4'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4508, c_4518, c_5107, c_5133])).
% 13.57/5.99  tff(c_5421, plain, (![A_317]: (m1_subset_1(k2_funct_1(A_317), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_317)), k1_relat_1(A_317)))) | ~v1_funct_1(k2_funct_1(A_317)) | ~v1_relat_1(k2_funct_1(A_317)) | ~v2_funct_1(A_317) | ~v1_funct_1(A_317) | ~v1_relat_1(A_317))), inference(superposition, [status(thm), theory('equality')], [c_32, c_333])).
% 13.57/5.99  tff(c_5457, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_2'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3449, c_5421])).
% 13.57/5.99  tff(c_5514, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_192, c_98, c_3296, c_4508, c_4518, c_5457])).
% 13.57/5.99  tff(c_5594, plain, (k5_relat_1(k2_funct_1('#skF_4'), k2_funct_1(k2_funct_1('#skF_4')))=k6_partfun1(k1_relat_1(k2_funct_1('#skF_4'))) | k1_xboole_0='#skF_2' | ~v2_funct_1(k2_funct_1('#skF_4')) | k2_relset_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_2', k2_funct_1('#skF_4'))!='#skF_2' | ~v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_5514, c_74])).
% 13.57/5.99  tff(c_5629, plain, (k5_relat_1(k2_funct_1('#skF_4'), k2_funct_1(k2_funct_1('#skF_4')))=k6_partfun1(k1_relat_1(k2_funct_1('#skF_4'))) | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4518, c_4568, c_5164, c_5387, c_5594])).
% 13.57/5.99  tff(c_5630, plain, (k5_relat_1(k2_funct_1('#skF_4'), k2_funct_1(k2_funct_1('#skF_4')))=k6_partfun1(k1_relat_1(k2_funct_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_84, c_5629])).
% 13.57/5.99  tff(c_42, plain, (![B_25, A_23]: (k5_relat_1(k2_funct_1(B_25), k2_funct_1(A_23))=k2_funct_1(k5_relat_1(A_23, B_25)) | ~v2_funct_1(B_25) | ~v2_funct_1(A_23) | ~v1_funct_1(B_25) | ~v1_relat_1(B_25) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.57/5.99  tff(c_5666, plain, (k6_partfun1(k1_relat_1(k2_funct_1('#skF_4')))=k2_funct_1(k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')) | ~v2_funct_1('#skF_4') | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5630, c_42])).
% 13.57/5.99  tff(c_5684, plain, (k6_partfun1(k1_relat_1(k2_funct_1('#skF_4')))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4508, c_4518, c_192, c_98, c_5387, c_3296, c_106, c_3295, c_5666])).
% 13.57/5.99  tff(c_5777, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5684, c_111])).
% 13.57/5.99  tff(c_5833, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_111, c_5777])).
% 13.57/5.99  tff(c_16, plain, (![D_16, B_10, A_9, C_14]: (D_16=B_10 | k6_relat_1(A_9)!=k5_relat_1(C_14, D_16) | k6_relat_1(k1_relat_1(D_16))!=k5_relat_1(B_10, C_14) | ~r1_tarski(k2_relat_1(B_10), A_9) | ~v1_relat_1(D_16) | ~v1_relat_1(C_14) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_60])).
% 13.57/5.99  tff(c_109, plain, (![D_16, B_10, A_9, C_14]: (D_16=B_10 | k6_partfun1(A_9)!=k5_relat_1(C_14, D_16) | k6_partfun1(k1_relat_1(D_16))!=k5_relat_1(B_10, C_14) | ~r1_tarski(k2_relat_1(B_10), A_9) | ~v1_relat_1(D_16) | ~v1_relat_1(C_14) | ~v1_relat_1(B_10))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_60, c_16])).
% 13.57/5.99  tff(c_3437, plain, (![B_10, A_9]: (k2_funct_1('#skF_4')=B_10 | k6_partfun1(A_9)!=k6_partfun1('#skF_2') | k6_partfun1(k1_relat_1(k2_funct_1('#skF_4')))!=k5_relat_1(B_10, '#skF_4') | ~r1_tarski(k2_relat_1(B_10), A_9) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1(B_10))), inference(superposition, [status(thm), theory('equality')], [c_3430, c_109])).
% 13.57/5.99  tff(c_3447, plain, (![B_10, A_9]: (k2_funct_1('#skF_4')=B_10 | k6_partfun1(A_9)!=k6_partfun1('#skF_2') | k6_partfun1(k1_relat_1(k2_funct_1('#skF_4')))!=k5_relat_1(B_10, '#skF_4') | ~r1_tarski(k2_relat_1(B_10), A_9) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(B_10))), inference(demodulation, [status(thm), theory('equality')], [c_192, c_3437])).
% 13.57/5.99  tff(c_15385, plain, (![B_468, A_469]: (k2_funct_1('#skF_4')=B_468 | k6_partfun1(A_469)!=k6_partfun1('#skF_2') | k5_relat_1(B_468, '#skF_4')!=k6_partfun1('#skF_1') | ~r1_tarski(k2_relat_1(B_468), A_469) | ~v1_relat_1(B_468))), inference(demodulation, [status(thm), theory('equality')], [c_4508, c_5833, c_3447])).
% 13.57/5.99  tff(c_15415, plain, (![A_469]: (k2_funct_1('#skF_4')='#skF_3' | k6_partfun1(A_469)!=k6_partfun1('#skF_2') | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | ~r1_tarski('#skF_2', A_469) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_310, c_15385])).
% 13.57/5.99  tff(c_15434, plain, (![A_469]: (k2_funct_1('#skF_4')='#skF_3' | k6_partfun1(A_469)!=k6_partfun1('#skF_2') | ~r1_tarski('#skF_2', A_469))), inference(demodulation, [status(thm), theory('equality')], [c_195, c_1831, c_15415])).
% 13.57/5.99  tff(c_15676, plain, (![A_470]: (k6_partfun1(A_470)!=k6_partfun1('#skF_2') | ~r1_tarski('#skF_2', A_470))), inference(splitLeft, [status(thm)], [c_15434])).
% 13.57/5.99  tff(c_15682, plain, $false, inference(resolution, [status(thm)], [c_6, c_15676])).
% 13.57/5.99  tff(c_15683, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_15434])).
% 13.57/5.99  tff(c_82, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_262])).
% 13.57/5.99  tff(c_4466, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_310, c_4442])).
% 13.57/5.99  tff(c_4491, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_195, c_104, c_88, c_4466])).
% 13.57/5.99  tff(c_4586, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_4491])).
% 13.57/5.99  tff(c_4589, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_4586])).
% 13.57/5.99  tff(c_4593, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_195, c_104, c_4589])).
% 13.57/5.99  tff(c_4595, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_4491])).
% 13.57/5.99  tff(c_3414, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_100, c_3402])).
% 13.57/5.99  tff(c_3433, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_92, c_88, c_3414])).
% 13.57/5.99  tff(c_3434, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_84, c_3433])).
% 13.57/5.99  tff(c_3505, plain, (k2_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3434, c_36])).
% 13.57/5.99  tff(c_3514, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_195, c_104, c_88, c_110, c_3505])).
% 13.57/5.99  tff(c_4594, plain, (~v1_funct_1(k2_funct_1('#skF_3')) | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_4491])).
% 13.57/5.99  tff(c_4596, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_4594])).
% 13.57/5.99  tff(c_4664, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_4596])).
% 13.57/5.99  tff(c_4668, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_195, c_104, c_4664])).
% 13.57/5.99  tff(c_4670, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_4594])).
% 13.57/5.99  tff(c_4906, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3'))))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_310, c_4852])).
% 13.57/5.99  tff(c_4945, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_195, c_104, c_88, c_4595, c_4670, c_4906])).
% 13.57/5.99  tff(c_5277, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3')))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_4945])).
% 13.57/5.99  tff(c_5311, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_195, c_104, c_88, c_3514, c_5277])).
% 13.57/5.99  tff(c_5371, plain, (k2_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_5311, c_46])).
% 13.57/5.99  tff(c_4669, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_4594])).
% 13.57/5.99  tff(c_4673, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_4669])).
% 13.57/5.99  tff(c_4675, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_195, c_104, c_88, c_3514, c_4673])).
% 13.57/5.99  tff(c_5320, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_1' | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_5311, c_72])).
% 13.57/5.99  tff(c_5354, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4670, c_4675, c_5320])).
% 13.57/5.99  tff(c_5355, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_86, c_5354])).
% 13.57/5.99  tff(c_5978, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relat_1(k2_funct_1('#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5371, c_5355])).
% 13.57/5.99  tff(c_5979, plain, (k2_relat_1(k2_funct_1('#skF_3'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_5978])).
% 13.57/5.99  tff(c_5982, plain, (k1_relat_1('#skF_3')!='#skF_1' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_5979])).
% 13.57/5.99  tff(c_5985, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_195, c_104, c_88, c_3514, c_5982])).
% 13.57/5.99  tff(c_5987, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(splitRight, [status(thm)], [c_5978])).
% 13.57/5.99  tff(c_3299, plain, (![B_10, A_9]: (B_10='#skF_4' | k6_partfun1(A_9)!=k6_partfun1('#skF_1') | k5_relat_1(B_10, k2_funct_1('#skF_4'))!=k6_partfun1(k1_relat_1('#skF_4')) | ~r1_tarski(k2_relat_1(B_10), A_9) | ~v1_relat_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(B_10))), inference(superposition, [status(thm), theory('equality')], [c_3295, c_109])).
% 13.57/5.99  tff(c_3303, plain, (![B_10, A_9]: (B_10='#skF_4' | k6_partfun1(A_9)!=k6_partfun1('#skF_1') | k5_relat_1(B_10, k2_funct_1('#skF_4'))!=k6_partfun1(k1_relat_1('#skF_4')) | ~r1_tarski(k2_relat_1(B_10), A_9) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(B_10))), inference(demodulation, [status(thm), theory('equality')], [c_192, c_3299])).
% 13.57/5.99  tff(c_14641, plain, (![B_463, A_464]: (B_463='#skF_4' | k6_partfun1(A_464)!=k6_partfun1('#skF_1') | k5_relat_1(B_463, k2_funct_1('#skF_4'))!=k6_partfun1('#skF_2') | ~r1_tarski(k2_relat_1(B_463), A_464) | ~v1_relat_1(B_463))), inference(demodulation, [status(thm), theory('equality')], [c_4508, c_3449, c_3303])).
% 13.57/5.99  tff(c_14653, plain, (![A_464]: (k2_funct_1('#skF_3')='#skF_4' | k6_partfun1(A_464)!=k6_partfun1('#skF_1') | k5_relat_1(k2_funct_1('#skF_3'), k2_funct_1('#skF_4'))!=k6_partfun1('#skF_2') | ~r1_tarski('#skF_1', A_464) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5987, c_14641])).
% 13.57/5.99  tff(c_14683, plain, (![A_464]: (k2_funct_1('#skF_3')='#skF_4' | k6_partfun1(A_464)!=k6_partfun1('#skF_1') | k5_relat_1(k2_funct_1('#skF_3'), k2_funct_1('#skF_4'))!=k6_partfun1('#skF_2') | ~r1_tarski('#skF_1', A_464))), inference(demodulation, [status(thm), theory('equality')], [c_4595, c_14653])).
% 13.57/5.99  tff(c_14684, plain, (![A_464]: (k6_partfun1(A_464)!=k6_partfun1('#skF_1') | k5_relat_1(k2_funct_1('#skF_3'), k2_funct_1('#skF_4'))!=k6_partfun1('#skF_2') | ~r1_tarski('#skF_1', A_464))), inference(negUnitSimplification, [status(thm)], [c_82, c_14683])).
% 13.57/5.99  tff(c_14698, plain, (k5_relat_1(k2_funct_1('#skF_3'), k2_funct_1('#skF_4'))!=k6_partfun1('#skF_2')), inference(splitLeft, [status(thm)], [c_14684])).
% 13.57/5.99  tff(c_15688, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_15683, c_14698])).
% 13.57/5.99  tff(c_15726, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1882, c_15688])).
% 13.57/5.99  tff(c_15729, plain, (![A_471]: (k6_partfun1(A_471)!=k6_partfun1('#skF_1') | ~r1_tarski('#skF_1', A_471))), inference(splitRight, [status(thm)], [c_14684])).
% 13.57/5.99  tff(c_15735, plain, $false, inference(resolution, [status(thm)], [c_6, c_15729])).
% 13.57/5.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.57/5.99  
% 13.57/5.99  Inference rules
% 13.57/5.99  ----------------------
% 13.57/5.99  #Ref     : 0
% 13.57/5.99  #Sup     : 3468
% 13.57/5.99  #Fact    : 0
% 13.57/5.99  #Define  : 0
% 13.57/5.99  #Split   : 43
% 13.57/5.99  #Chain   : 0
% 13.57/5.99  #Close   : 0
% 13.57/5.99  
% 13.57/5.99  Ordering : KBO
% 13.57/5.99  
% 13.57/5.99  Simplification rules
% 13.57/5.99  ----------------------
% 13.57/5.99  #Subsume      : 255
% 13.57/5.99  #Demod        : 8012
% 13.57/5.99  #Tautology    : 1062
% 13.57/5.99  #SimpNegUnit  : 274
% 13.57/5.99  #BackRed      : 155
% 13.57/5.99  
% 13.57/5.99  #Partial instantiations: 0
% 13.57/5.99  #Strategies tried      : 1
% 13.57/5.99  
% 13.57/5.99  Timing (in seconds)
% 13.57/5.99  ----------------------
% 13.57/6.00  Preprocessing        : 0.40
% 13.57/6.00  Parsing              : 0.20
% 13.57/6.00  CNF conversion       : 0.03
% 13.57/6.00  Main loop            : 4.75
% 13.57/6.00  Inferencing          : 1.07
% 13.57/6.00  Reduction            : 2.53
% 13.57/6.00  Demodulation         : 2.18
% 13.57/6.00  BG Simplification    : 0.11
% 13.57/6.00  Subsumption          : 0.79
% 13.57/6.00  Abstraction          : 0.15
% 13.57/6.00  MUC search           : 0.00
% 13.57/6.00  Cooper               : 0.00
% 13.57/6.00  Total                : 5.24
% 13.57/6.00  Index Insertion      : 0.00
% 13.57/6.00  Index Deletion       : 0.00
% 13.57/6.00  Index Matching       : 0.00
% 13.57/6.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
