%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:16 EST 2020

% Result     : Theorem 14.14s
% Output     : CNFRefutation 14.44s
% Verified   : 
% Statistics : Number of formulae       :  217 (17876 expanded)
%              Number of leaves         :   46 (6230 expanded)
%              Depth                    :   28
%              Number of atoms          :  571 (70504 expanded)
%              Number of equality atoms :  188 (21666 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_219,negated_conjecture,(
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

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_122,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_134,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_110,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_108,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_132,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

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

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_193,axiom,(
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

tff(f_151,axiom,(
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

tff(f_96,axiom,(
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

tff(f_79,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

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
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_69,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_177,axiom,(
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

tff(c_64,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_86,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_74,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_82,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_243,plain,(
    ! [A_86,B_87,C_88] :
      ( k2_relset_1(A_86,B_87,C_88) = k2_relat_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_249,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_243])).

tff(c_256,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_249])).

tff(c_80,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_76,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_1525,plain,(
    ! [C_171,A_170,D_173,B_172,E_169,F_168] :
      ( m1_subset_1(k1_partfun1(A_170,B_172,C_171,D_173,E_169,F_168),k1_zfmisc_1(k2_zfmisc_1(A_170,D_173)))
      | ~ m1_subset_1(F_168,k1_zfmisc_1(k2_zfmisc_1(C_171,D_173)))
      | ~ v1_funct_1(F_168)
      | ~ m1_subset_1(E_169,k1_zfmisc_1(k2_zfmisc_1(A_170,B_172)))
      | ~ v1_funct_1(E_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_48,plain,(
    ! [A_40] : k6_relat_1(A_40) = k6_partfun1(A_40) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_40,plain,(
    ! [A_27] : m1_subset_1(k6_relat_1(A_27),k1_zfmisc_1(k2_zfmisc_1(A_27,A_27))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_87,plain,(
    ! [A_27] : m1_subset_1(k6_partfun1(A_27),k1_zfmisc_1(k2_zfmisc_1(A_27,A_27))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40])).

tff(c_72,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_461,plain,(
    ! [D_104,C_105,A_106,B_107] :
      ( D_104 = C_105
      | ~ r2_relset_1(A_106,B_107,C_105,D_104)
      | ~ m1_subset_1(D_104,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107)))
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_469,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_72,c_461])).

tff(c_484,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_469])).

tff(c_659,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_484])).

tff(c_1548,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1525,c_659])).

tff(c_1574,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_80,c_76,c_1548])).

tff(c_1575,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_484])).

tff(c_8243,plain,(
    ! [C_513,F_510,D_509,E_511,A_508,B_512] :
      ( k1_partfun1(A_508,B_512,C_513,D_509,E_511,F_510) = k5_relat_1(E_511,F_510)
      | ~ m1_subset_1(F_510,k1_zfmisc_1(k2_zfmisc_1(C_513,D_509)))
      | ~ v1_funct_1(F_510)
      | ~ m1_subset_1(E_511,k1_zfmisc_1(k2_zfmisc_1(A_508,B_512)))
      | ~ v1_funct_1(E_511) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_8249,plain,(
    ! [A_508,B_512,E_511] :
      ( k1_partfun1(A_508,B_512,'#skF_2','#skF_1',E_511,'#skF_4') = k5_relat_1(E_511,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_511,k1_zfmisc_1(k2_zfmisc_1(A_508,B_512)))
      | ~ v1_funct_1(E_511) ) ),
    inference(resolution,[status(thm)],[c_76,c_8243])).

tff(c_10291,plain,(
    ! [A_592,B_593,E_594] :
      ( k1_partfun1(A_592,B_593,'#skF_2','#skF_1',E_594,'#skF_4') = k5_relat_1(E_594,'#skF_4')
      | ~ m1_subset_1(E_594,k1_zfmisc_1(k2_zfmisc_1(A_592,B_593)))
      | ~ v1_funct_1(E_594) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_8249])).

tff(c_10306,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_10291])).

tff(c_10320,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1575,c_10306])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_130,plain,(
    ! [B_66,A_67] :
      ( v1_relat_1(B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_67))
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_136,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_82,c_130])).

tff(c_145,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_136])).

tff(c_139,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_76,c_130])).

tff(c_148,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_139])).

tff(c_24,plain,(
    ! [A_14] :
      ( v1_relat_1(k2_funct_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_78,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_257,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_243])).

tff(c_2270,plain,(
    ! [B_216,C_217,A_218] :
      ( k6_partfun1(B_216) = k5_relat_1(k2_funct_1(C_217),C_217)
      | k1_xboole_0 = B_216
      | ~ v2_funct_1(C_217)
      | k2_relset_1(A_218,B_216,C_217) != B_216
      | ~ m1_subset_1(C_217,k1_zfmisc_1(k2_zfmisc_1(A_218,B_216)))
      | ~ v1_funct_2(C_217,A_218,B_216)
      | ~ v1_funct_1(C_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_2276,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_2270])).

tff(c_2286,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_257,c_2276])).

tff(c_2287,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2286])).

tff(c_2297,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2287])).

tff(c_84,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_233,plain,(
    ! [A_83,B_84,D_85] :
      ( r2_relset_1(A_83,B_84,D_85,D_85)
      | ~ m1_subset_1(D_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_240,plain,(
    ! [A_27] : r2_relset_1(A_27,A_27,k6_partfun1(A_27),k6_partfun1(A_27)) ),
    inference(resolution,[status(thm)],[c_87,c_233])).

tff(c_3342,plain,(
    ! [A_265,B_266,C_267,D_268] :
      ( k2_relset_1(A_265,B_266,C_267) = B_266
      | ~ r2_relset_1(B_266,B_266,k1_partfun1(B_266,A_265,A_265,B_266,D_268,C_267),k6_partfun1(B_266))
      | ~ m1_subset_1(D_268,k1_zfmisc_1(k2_zfmisc_1(B_266,A_265)))
      | ~ v1_funct_2(D_268,B_266,A_265)
      | ~ v1_funct_1(D_268)
      | ~ m1_subset_1(C_267,k1_zfmisc_1(k2_zfmisc_1(A_265,B_266)))
      | ~ v1_funct_2(C_267,A_265,B_266)
      | ~ v1_funct_1(C_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_3351,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1575,c_3342])).

tff(c_3358,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_86,c_84,c_82,c_240,c_257,c_3351])).

tff(c_3360,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2297,c_3358])).

tff(c_3362,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2287])).

tff(c_70,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_32,plain,(
    ! [A_17,B_19] :
      ( k2_funct_1(A_17) = B_19
      | k6_relat_1(k2_relat_1(A_17)) != k5_relat_1(B_19,A_17)
      | k2_relat_1(B_19) != k1_relat_1(A_17)
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1800,plain,(
    ! [A_181,B_182] :
      ( k2_funct_1(A_181) = B_182
      | k6_partfun1(k2_relat_1(A_181)) != k5_relat_1(B_182,A_181)
      | k2_relat_1(B_182) != k1_relat_1(A_181)
      | ~ v2_funct_1(A_181)
      | ~ v1_funct_1(B_182)
      | ~ v1_relat_1(B_182)
      | ~ v1_funct_1(A_181)
      | ~ v1_relat_1(A_181) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_32])).

tff(c_1818,plain,(
    ! [B_182] :
      ( k2_funct_1('#skF_3') = B_182
      | k5_relat_1(B_182,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_182) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_182)
      | ~ v1_relat_1(B_182)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_1800])).

tff(c_1843,plain,(
    ! [B_185] :
      ( k2_funct_1('#skF_3') = B_185
      | k5_relat_1(B_185,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_185) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_185)
      | ~ v1_relat_1(B_185) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_86,c_70,c_1818])).

tff(c_1852,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_148,c_1843])).

tff(c_1868,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1852])).

tff(c_1869,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1868])).

tff(c_1875,plain,(
    k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1869])).

tff(c_3363,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3362,c_1875])).

tff(c_215,plain,(
    ! [A_82] :
      ( k1_relat_1(k2_funct_1(A_82)) = k2_relat_1(A_82)
      | ~ v2_funct_1(A_82)
      | ~ v1_funct_1(A_82)
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_167,plain,(
    ! [B_75,A_76] :
      ( v4_relat_1(B_75,A_76)
      | ~ r1_tarski(k1_relat_1(B_75),A_76)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_181,plain,(
    ! [B_75] :
      ( v4_relat_1(B_75,k1_relat_1(B_75))
      | ~ v1_relat_1(B_75) ) ),
    inference(resolution,[status(thm)],[c_6,c_167])).

tff(c_315,plain,(
    ! [A_95] :
      ( v4_relat_1(k2_funct_1(A_95),k2_relat_1(A_95))
      | ~ v1_relat_1(k2_funct_1(A_95))
      | ~ v2_funct_1(A_95)
      | ~ v1_funct_1(A_95)
      | ~ v1_relat_1(A_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_181])).

tff(c_318,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_315])).

tff(c_326,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_86,c_70,c_318])).

tff(c_356,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_326])).

tff(c_359,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_356])).

tff(c_363,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_86,c_359])).

tff(c_365,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_326])).

tff(c_364,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_326])).

tff(c_20,plain,(
    ! [A_13] : k2_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_90,plain,(
    ! [A_13] : k2_relat_1(k6_partfun1(A_13)) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_20])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_3497,plain,(
    ! [A_270,C_271,B_272] :
      ( k6_partfun1(A_270) = k5_relat_1(C_271,k2_funct_1(C_271))
      | k1_xboole_0 = B_272
      | ~ v2_funct_1(C_271)
      | k2_relset_1(A_270,B_272,C_271) != B_272
      | ~ m1_subset_1(C_271,k1_zfmisc_1(k2_zfmisc_1(A_270,B_272)))
      | ~ v1_funct_2(C_271,A_270,B_272)
      | ~ v1_funct_1(C_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_3501,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_3497])).

tff(c_3509,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_74,c_70,c_3501])).

tff(c_3510,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_3509])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_329,plain,(
    ! [B_96,A_97] :
      ( k2_relat_1(k5_relat_1(B_96,A_97)) = k2_relat_1(A_97)
      | ~ r1_tarski(k1_relat_1(A_97),k2_relat_1(B_96))
      | ~ v1_relat_1(B_96)
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_332,plain,(
    ! [A_97] :
      ( k2_relat_1(k5_relat_1('#skF_3',A_97)) = k2_relat_1(A_97)
      | ~ r1_tarski(k1_relat_1(A_97),'#skF_2')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(A_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_329])).

tff(c_366,plain,(
    ! [A_98] :
      ( k2_relat_1(k5_relat_1('#skF_3',A_98)) = k2_relat_1(A_98)
      | ~ r1_tarski(k1_relat_1(A_98),'#skF_2')
      | ~ v1_relat_1(A_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_332])).

tff(c_377,plain,(
    ! [B_7] :
      ( k2_relat_1(k5_relat_1('#skF_3',B_7)) = k2_relat_1(B_7)
      | ~ v4_relat_1(B_7,'#skF_2')
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_366])).

tff(c_3520,plain,
    ( k2_relat_1(k6_partfun1('#skF_1')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3510,c_377])).

tff(c_3524,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_364,c_90,c_3520])).

tff(c_28,plain,(
    ! [A_16] :
      ( k2_relat_1(k2_funct_1(A_16)) = k1_relat_1(A_16)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3546,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3524,c_28])).

tff(c_3565,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_86,c_70,c_3546])).

tff(c_3567,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3363,c_3565])).

tff(c_3569,plain,(
    k2_relat_1('#skF_4') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1869])).

tff(c_221,plain,(
    ! [A_82] :
      ( v4_relat_1(k2_funct_1(A_82),k2_relat_1(A_82))
      | ~ v1_relat_1(k2_funct_1(A_82))
      | ~ v2_funct_1(A_82)
      | ~ v1_funct_1(A_82)
      | ~ v1_relat_1(A_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_181])).

tff(c_3585,plain,
    ( v4_relat_1(k2_funct_1('#skF_4'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3569,c_221])).

tff(c_3597,plain,
    ( v4_relat_1(k2_funct_1('#skF_4'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_80,c_3585])).

tff(c_3634,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3597])).

tff(c_26,plain,(
    ! [A_15] : v2_funct_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_89,plain,(
    ! [A_15] : v2_funct_1(k6_partfun1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_26])).

tff(c_6220,plain,(
    ! [A_409,C_408,D_407,B_406,E_405] :
      ( k1_xboole_0 = C_408
      | v2_funct_1(E_405)
      | k2_relset_1(A_409,B_406,D_407) != B_406
      | ~ v2_funct_1(k1_partfun1(A_409,B_406,B_406,C_408,D_407,E_405))
      | ~ m1_subset_1(E_405,k1_zfmisc_1(k2_zfmisc_1(B_406,C_408)))
      | ~ v1_funct_2(E_405,B_406,C_408)
      | ~ v1_funct_1(E_405)
      | ~ m1_subset_1(D_407,k1_zfmisc_1(k2_zfmisc_1(A_409,B_406)))
      | ~ v1_funct_2(D_407,A_409,B_406)
      | ~ v1_funct_1(D_407) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_6224,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_1575,c_6220])).

tff(c_6229,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_80,c_78,c_76,c_89,c_74,c_6224])).

tff(c_6231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3634,c_68,c_6229])).

tff(c_6232,plain,
    ( ~ v1_relat_1(k2_funct_1('#skF_4'))
    | v4_relat_1(k2_funct_1('#skF_4'),k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3597])).

tff(c_6234,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_6232])).

tff(c_6237,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_6234])).

tff(c_6241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_80,c_6237])).

tff(c_6243,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_6232])).

tff(c_22,plain,(
    ! [A_14] :
      ( v1_funct_1(k2_funct_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6233,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_3597])).

tff(c_8322,plain,(
    ! [A_520,C_521,B_522] :
      ( k6_partfun1(A_520) = k5_relat_1(C_521,k2_funct_1(C_521))
      | k1_xboole_0 = B_522
      | ~ v2_funct_1(C_521)
      | k2_relset_1(A_520,B_522,C_521) != B_522
      | ~ m1_subset_1(C_521,k1_zfmisc_1(k2_zfmisc_1(A_520,B_522)))
      | ~ v1_funct_2(C_521,A_520,B_522)
      | ~ v1_funct_1(C_521) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_8326,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_8322])).

tff(c_8334,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_74,c_70,c_8326])).

tff(c_8335,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_8334])).

tff(c_8343,plain,
    ( k2_relat_1(k6_partfun1('#skF_1')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8335,c_377])).

tff(c_8347,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_364,c_90,c_8343])).

tff(c_8366,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8347,c_28])).

tff(c_8383,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_86,c_70,c_8366])).

tff(c_8401,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8383,c_3569])).

tff(c_30,plain,(
    ! [A_16] :
      ( k1_relat_1(k2_funct_1(A_16)) = k2_relat_1(A_16)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_6242,plain,(
    v4_relat_1(k2_funct_1('#skF_4'),k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_6232])).

tff(c_157,plain,(
    ! [B_71,A_72] :
      ( r1_tarski(k1_relat_1(B_71),A_72)
      | ~ v4_relat_1(B_71,A_72)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_276,plain,(
    ! [B_91,A_92] :
      ( k1_relat_1(B_91) = A_92
      | ~ r1_tarski(A_92,k1_relat_1(B_91))
      | ~ v4_relat_1(B_91,A_92)
      | ~ v1_relat_1(B_91) ) ),
    inference(resolution,[status(thm)],[c_157,c_2])).

tff(c_291,plain,(
    ! [B_91,B_7] :
      ( k1_relat_1(B_91) = k1_relat_1(B_7)
      | ~ v4_relat_1(B_91,k1_relat_1(B_7))
      | ~ v1_relat_1(B_91)
      | ~ v4_relat_1(B_7,k1_relat_1(B_91))
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_276])).

tff(c_6250,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v4_relat_1('#skF_3',k1_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6242,c_291])).

tff(c_6253,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_3')
    | ~ v4_relat_1('#skF_3',k1_relat_1(k2_funct_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_6243,c_6250])).

tff(c_6254,plain,(
    ~ v4_relat_1('#skF_3',k1_relat_1(k2_funct_1('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_6253])).

tff(c_6257,plain,
    ( ~ v4_relat_1('#skF_3',k2_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_6254])).

tff(c_6259,plain,(
    ~ v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_80,c_6233,c_3569,c_6257])).

tff(c_6276,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_181,c_6259])).

tff(c_6280,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_6276])).

tff(c_6281,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_6253])).

tff(c_8396,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8383,c_6281])).

tff(c_3570,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3569,c_257])).

tff(c_8328,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_8322])).

tff(c_8338,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_3570,c_6233,c_8328])).

tff(c_8339,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_8338])).

tff(c_8447,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8383,c_8339])).

tff(c_351,plain,(
    ! [B_96,B_7] :
      ( k2_relat_1(k5_relat_1(B_96,B_7)) = k2_relat_1(B_7)
      | ~ v1_relat_1(B_96)
      | ~ v4_relat_1(B_7,k2_relat_1(B_96))
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_329])).

tff(c_3579,plain,(
    ! [B_7] :
      ( k2_relat_1(k5_relat_1('#skF_4',B_7)) = k2_relat_1(B_7)
      | ~ v1_relat_1('#skF_4')
      | ~ v4_relat_1(B_7,k1_relat_1('#skF_3'))
      | ~ v1_relat_1(B_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3569,c_351])).

tff(c_6343,plain,(
    ! [B_416] :
      ( k2_relat_1(k5_relat_1('#skF_4',B_416)) = k2_relat_1(B_416)
      | ~ v4_relat_1(B_416,k1_relat_1('#skF_3'))
      | ~ v1_relat_1(B_416) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_3579])).

tff(c_6349,plain,
    ( k2_relat_1(k5_relat_1('#skF_4',k2_funct_1('#skF_4'))) = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6242,c_6343])).

tff(c_6371,plain,(
    k2_relat_1(k5_relat_1('#skF_4',k2_funct_1('#skF_4'))) = k2_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6243,c_6349])).

tff(c_8448,plain,(
    k2_relat_1(k6_partfun1('#skF_2')) = k2_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8447,c_6371])).

tff(c_8449,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_8448])).

tff(c_8519,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8449,c_28])).

tff(c_8536,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_80,c_6233,c_8519])).

tff(c_16519,plain,(
    ! [A_751,B_752] :
      ( k2_funct_1(k2_funct_1(A_751)) = B_752
      | k5_relat_1(B_752,k2_funct_1(A_751)) != k6_partfun1(k1_relat_1(A_751))
      | k2_relat_1(B_752) != k1_relat_1(k2_funct_1(A_751))
      | ~ v2_funct_1(k2_funct_1(A_751))
      | ~ v1_funct_1(B_752)
      | ~ v1_relat_1(B_752)
      | ~ v1_funct_1(k2_funct_1(A_751))
      | ~ v1_relat_1(k2_funct_1(A_751))
      | ~ v2_funct_1(A_751)
      | ~ v1_funct_1(A_751)
      | ~ v1_relat_1(A_751) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1800])).

tff(c_16521,plain,
    ( k2_funct_1(k2_funct_1('#skF_4')) = '#skF_4'
    | k6_partfun1(k1_relat_1('#skF_4')) != k6_partfun1('#skF_2')
    | k1_relat_1(k2_funct_1('#skF_4')) != k2_relat_1('#skF_4')
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8447,c_16519])).

tff(c_16525,plain,
    ( k2_funct_1(k2_funct_1('#skF_4')) = '#skF_4'
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_80,c_6233,c_6243,c_148,c_80,c_8401,c_8396,c_8536,c_16521])).

tff(c_16528,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_16525])).

tff(c_16531,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_16528])).

tff(c_16535,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_80,c_16531])).

tff(c_16537,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_16525])).

tff(c_88,plain,(
    ! [A_17,B_19] :
      ( k2_funct_1(A_17) = B_19
      | k6_partfun1(k2_relat_1(A_17)) != k5_relat_1(B_19,A_17)
      | k2_relat_1(B_19) != k1_relat_1(A_17)
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_32])).

tff(c_8456,plain,(
    ! [B_19] :
      ( k2_funct_1('#skF_4') = B_19
      | k5_relat_1(B_19,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_19) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8401,c_88])).

tff(c_8472,plain,(
    ! [B_19] :
      ( k2_funct_1('#skF_4') = B_19
      | k5_relat_1(B_19,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_19) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_80,c_6233,c_8456])).

tff(c_24323,plain,(
    ! [B_880] :
      ( k2_funct_1('#skF_4') = B_880
      | k5_relat_1(B_880,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_880) != '#skF_2'
      | ~ v1_funct_1(B_880)
      | ~ v1_relat_1(B_880) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8536,c_8472])).

tff(c_24551,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_145,c_24323])).

tff(c_24759,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_256,c_10320,c_24551])).

tff(c_16536,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_4'))
    | k2_funct_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_16525])).

tff(c_16539,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_16536])).

tff(c_24765,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24759,c_16539])).

tff(c_24784,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_24765])).

tff(c_24786,plain,(
    v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_16536])).

tff(c_24785,plain,(
    k2_funct_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_16536])).

tff(c_1820,plain,(
    ! [A_16,B_182] :
      ( k2_funct_1(k2_funct_1(A_16)) = B_182
      | k5_relat_1(B_182,k2_funct_1(A_16)) != k6_partfun1(k1_relat_1(A_16))
      | k2_relat_1(B_182) != k1_relat_1(k2_funct_1(A_16))
      | ~ v2_funct_1(k2_funct_1(A_16))
      | ~ v1_funct_1(B_182)
      | ~ v1_relat_1(B_182)
      | ~ v1_funct_1(k2_funct_1(A_16))
      | ~ v1_relat_1(k2_funct_1(A_16))
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1800])).

tff(c_24789,plain,(
    ! [B_182] :
      ( k2_funct_1(k2_funct_1(k2_funct_1('#skF_4'))) = B_182
      | k6_partfun1(k1_relat_1(k2_funct_1('#skF_4'))) != k5_relat_1(B_182,'#skF_4')
      | k2_relat_1(B_182) != k1_relat_1(k2_funct_1(k2_funct_1('#skF_4')))
      | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_4')))
      | ~ v1_funct_1(B_182)
      | ~ v1_relat_1(B_182)
      | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_4')))
      | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_4')))
      | ~ v2_funct_1(k2_funct_1('#skF_4'))
      | ~ v1_funct_1(k2_funct_1('#skF_4'))
      | ~ v1_relat_1(k2_funct_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24785,c_1820])).

tff(c_27078,plain,(
    ! [B_942] :
      ( k2_funct_1('#skF_4') = B_942
      | k5_relat_1(B_942,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_942) != '#skF_2'
      | ~ v1_funct_1(B_942)
      | ~ v1_relat_1(B_942) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6243,c_16537,c_24786,c_148,c_24785,c_80,c_24785,c_6233,c_24785,c_8536,c_24785,c_8396,c_24785,c_24789])).

tff(c_27183,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_145,c_27078])).

tff(c_27289,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_256,c_10320,c_27183])).

tff(c_27296,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27289,c_24785])).

tff(c_27315,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_27296])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:57:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.14/7.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.14/7.22  
% 14.14/7.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.14/7.23  %$ r2_relset_1 > v1_funct_2 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 14.14/7.23  
% 14.14/7.23  %Foreground sorts:
% 14.14/7.23  
% 14.14/7.23  
% 14.14/7.23  %Background operators:
% 14.14/7.23  
% 14.14/7.23  
% 14.14/7.23  %Foreground operators:
% 14.14/7.23  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 14.14/7.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 14.14/7.23  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 14.14/7.23  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 14.14/7.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.14/7.23  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 14.14/7.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.14/7.23  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 14.14/7.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.14/7.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 14.14/7.23  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 14.14/7.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 14.14/7.23  tff('#skF_2', type, '#skF_2': $i).
% 14.14/7.23  tff('#skF_3', type, '#skF_3': $i).
% 14.14/7.23  tff('#skF_1', type, '#skF_1': $i).
% 14.14/7.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.14/7.23  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 14.14/7.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.14/7.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.14/7.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.14/7.23  tff('#skF_4', type, '#skF_4': $i).
% 14.14/7.23  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 14.14/7.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.14/7.23  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 14.14/7.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.14/7.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.14/7.23  
% 14.44/7.26  tff(f_219, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 14.44/7.26  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 14.44/7.26  tff(f_122, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 14.44/7.26  tff(f_134, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 14.44/7.26  tff(f_110, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 14.44/7.26  tff(f_108, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 14.44/7.26  tff(f_132, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 14.44/7.26  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 14.44/7.26  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 14.44/7.26  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 14.44/7.26  tff(f_193, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 14.44/7.26  tff(f_151, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 14.44/7.26  tff(f_96, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 14.44/7.26  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 14.44/7.26  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.44/7.26  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 14.44/7.26  tff(f_59, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 14.44/7.26  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 14.44/7.26  tff(f_69, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 14.44/7.26  tff(f_177, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 14.44/7.26  tff(c_64, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_219])).
% 14.44/7.26  tff(c_86, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_219])).
% 14.44/7.26  tff(c_74, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_219])).
% 14.44/7.26  tff(c_82, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_219])).
% 14.44/7.26  tff(c_243, plain, (![A_86, B_87, C_88]: (k2_relset_1(A_86, B_87, C_88)=k2_relat_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 14.44/7.26  tff(c_249, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_243])).
% 14.44/7.26  tff(c_256, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_249])).
% 14.44/7.26  tff(c_80, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_219])).
% 14.44/7.26  tff(c_76, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_219])).
% 14.44/7.26  tff(c_1525, plain, (![C_171, A_170, D_173, B_172, E_169, F_168]: (m1_subset_1(k1_partfun1(A_170, B_172, C_171, D_173, E_169, F_168), k1_zfmisc_1(k2_zfmisc_1(A_170, D_173))) | ~m1_subset_1(F_168, k1_zfmisc_1(k2_zfmisc_1(C_171, D_173))) | ~v1_funct_1(F_168) | ~m1_subset_1(E_169, k1_zfmisc_1(k2_zfmisc_1(A_170, B_172))) | ~v1_funct_1(E_169))), inference(cnfTransformation, [status(thm)], [f_122])).
% 14.44/7.26  tff(c_48, plain, (![A_40]: (k6_relat_1(A_40)=k6_partfun1(A_40))), inference(cnfTransformation, [status(thm)], [f_134])).
% 14.44/7.26  tff(c_40, plain, (![A_27]: (m1_subset_1(k6_relat_1(A_27), k1_zfmisc_1(k2_zfmisc_1(A_27, A_27))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 14.44/7.26  tff(c_87, plain, (![A_27]: (m1_subset_1(k6_partfun1(A_27), k1_zfmisc_1(k2_zfmisc_1(A_27, A_27))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40])).
% 14.44/7.26  tff(c_72, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_219])).
% 14.44/7.26  tff(c_461, plain, (![D_104, C_105, A_106, B_107]: (D_104=C_105 | ~r2_relset_1(A_106, B_107, C_105, D_104) | ~m1_subset_1(D_104, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 14.44/7.26  tff(c_469, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_72, c_461])).
% 14.44/7.26  tff(c_484, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_469])).
% 14.44/7.26  tff(c_659, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_484])).
% 14.44/7.26  tff(c_1548, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1525, c_659])).
% 14.44/7.26  tff(c_1574, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_80, c_76, c_1548])).
% 14.44/7.26  tff(c_1575, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_484])).
% 14.44/7.26  tff(c_8243, plain, (![C_513, F_510, D_509, E_511, A_508, B_512]: (k1_partfun1(A_508, B_512, C_513, D_509, E_511, F_510)=k5_relat_1(E_511, F_510) | ~m1_subset_1(F_510, k1_zfmisc_1(k2_zfmisc_1(C_513, D_509))) | ~v1_funct_1(F_510) | ~m1_subset_1(E_511, k1_zfmisc_1(k2_zfmisc_1(A_508, B_512))) | ~v1_funct_1(E_511))), inference(cnfTransformation, [status(thm)], [f_132])).
% 14.44/7.26  tff(c_8249, plain, (![A_508, B_512, E_511]: (k1_partfun1(A_508, B_512, '#skF_2', '#skF_1', E_511, '#skF_4')=k5_relat_1(E_511, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_511, k1_zfmisc_1(k2_zfmisc_1(A_508, B_512))) | ~v1_funct_1(E_511))), inference(resolution, [status(thm)], [c_76, c_8243])).
% 14.44/7.26  tff(c_10291, plain, (![A_592, B_593, E_594]: (k1_partfun1(A_592, B_593, '#skF_2', '#skF_1', E_594, '#skF_4')=k5_relat_1(E_594, '#skF_4') | ~m1_subset_1(E_594, k1_zfmisc_1(k2_zfmisc_1(A_592, B_593))) | ~v1_funct_1(E_594))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_8249])).
% 14.44/7.26  tff(c_10306, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_10291])).
% 14.44/7.26  tff(c_10320, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1575, c_10306])).
% 14.44/7.26  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 14.44/7.26  tff(c_130, plain, (![B_66, A_67]: (v1_relat_1(B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(A_67)) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_38])).
% 14.44/7.26  tff(c_136, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_82, c_130])).
% 14.44/7.26  tff(c_145, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_136])).
% 14.44/7.26  tff(c_139, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_76, c_130])).
% 14.44/7.26  tff(c_148, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_139])).
% 14.44/7.26  tff(c_24, plain, (![A_14]: (v1_relat_1(k2_funct_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_67])).
% 14.44/7.26  tff(c_68, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_219])).
% 14.44/7.26  tff(c_78, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_219])).
% 14.44/7.26  tff(c_257, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_243])).
% 14.44/7.26  tff(c_2270, plain, (![B_216, C_217, A_218]: (k6_partfun1(B_216)=k5_relat_1(k2_funct_1(C_217), C_217) | k1_xboole_0=B_216 | ~v2_funct_1(C_217) | k2_relset_1(A_218, B_216, C_217)!=B_216 | ~m1_subset_1(C_217, k1_zfmisc_1(k2_zfmisc_1(A_218, B_216))) | ~v1_funct_2(C_217, A_218, B_216) | ~v1_funct_1(C_217))), inference(cnfTransformation, [status(thm)], [f_193])).
% 14.44/7.26  tff(c_2276, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_2270])).
% 14.44/7.26  tff(c_2286, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_257, c_2276])).
% 14.44/7.26  tff(c_2287, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_68, c_2286])).
% 14.44/7.26  tff(c_2297, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2287])).
% 14.44/7.26  tff(c_84, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_219])).
% 14.44/7.26  tff(c_233, plain, (![A_83, B_84, D_85]: (r2_relset_1(A_83, B_84, D_85, D_85) | ~m1_subset_1(D_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 14.44/7.26  tff(c_240, plain, (![A_27]: (r2_relset_1(A_27, A_27, k6_partfun1(A_27), k6_partfun1(A_27)))), inference(resolution, [status(thm)], [c_87, c_233])).
% 14.44/7.26  tff(c_3342, plain, (![A_265, B_266, C_267, D_268]: (k2_relset_1(A_265, B_266, C_267)=B_266 | ~r2_relset_1(B_266, B_266, k1_partfun1(B_266, A_265, A_265, B_266, D_268, C_267), k6_partfun1(B_266)) | ~m1_subset_1(D_268, k1_zfmisc_1(k2_zfmisc_1(B_266, A_265))) | ~v1_funct_2(D_268, B_266, A_265) | ~v1_funct_1(D_268) | ~m1_subset_1(C_267, k1_zfmisc_1(k2_zfmisc_1(A_265, B_266))) | ~v1_funct_2(C_267, A_265, B_266) | ~v1_funct_1(C_267))), inference(cnfTransformation, [status(thm)], [f_151])).
% 14.44/7.26  tff(c_3351, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1575, c_3342])).
% 14.44/7.26  tff(c_3358, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_86, c_84, c_82, c_240, c_257, c_3351])).
% 14.44/7.26  tff(c_3360, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2297, c_3358])).
% 14.44/7.26  tff(c_3362, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_2287])).
% 14.44/7.26  tff(c_70, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_219])).
% 14.44/7.26  tff(c_32, plain, (![A_17, B_19]: (k2_funct_1(A_17)=B_19 | k6_relat_1(k2_relat_1(A_17))!=k5_relat_1(B_19, A_17) | k2_relat_1(B_19)!=k1_relat_1(A_17) | ~v2_funct_1(A_17) | ~v1_funct_1(B_19) | ~v1_relat_1(B_19) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_96])).
% 14.44/7.26  tff(c_1800, plain, (![A_181, B_182]: (k2_funct_1(A_181)=B_182 | k6_partfun1(k2_relat_1(A_181))!=k5_relat_1(B_182, A_181) | k2_relat_1(B_182)!=k1_relat_1(A_181) | ~v2_funct_1(A_181) | ~v1_funct_1(B_182) | ~v1_relat_1(B_182) | ~v1_funct_1(A_181) | ~v1_relat_1(A_181))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_32])).
% 14.44/7.26  tff(c_1818, plain, (![B_182]: (k2_funct_1('#skF_3')=B_182 | k5_relat_1(B_182, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_182)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_182) | ~v1_relat_1(B_182) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_256, c_1800])).
% 14.44/7.26  tff(c_1843, plain, (![B_185]: (k2_funct_1('#skF_3')=B_185 | k5_relat_1(B_185, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_185)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_185) | ~v1_relat_1(B_185))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_86, c_70, c_1818])).
% 14.44/7.26  tff(c_1852, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_148, c_1843])).
% 14.44/7.26  tff(c_1868, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1852])).
% 14.44/7.26  tff(c_1869, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_64, c_1868])).
% 14.44/7.26  tff(c_1875, plain, (k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_1869])).
% 14.44/7.26  tff(c_3363, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3362, c_1875])).
% 14.44/7.26  tff(c_215, plain, (![A_82]: (k1_relat_1(k2_funct_1(A_82))=k2_relat_1(A_82) | ~v2_funct_1(A_82) | ~v1_funct_1(A_82) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_79])).
% 14.44/7.26  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.44/7.26  tff(c_167, plain, (![B_75, A_76]: (v4_relat_1(B_75, A_76) | ~r1_tarski(k1_relat_1(B_75), A_76) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_44])).
% 14.44/7.26  tff(c_181, plain, (![B_75]: (v4_relat_1(B_75, k1_relat_1(B_75)) | ~v1_relat_1(B_75))), inference(resolution, [status(thm)], [c_6, c_167])).
% 14.44/7.26  tff(c_315, plain, (![A_95]: (v4_relat_1(k2_funct_1(A_95), k2_relat_1(A_95)) | ~v1_relat_1(k2_funct_1(A_95)) | ~v2_funct_1(A_95) | ~v1_funct_1(A_95) | ~v1_relat_1(A_95))), inference(superposition, [status(thm), theory('equality')], [c_215, c_181])).
% 14.44/7.26  tff(c_318, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_256, c_315])).
% 14.44/7.26  tff(c_326, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_86, c_70, c_318])).
% 14.44/7.26  tff(c_356, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_326])).
% 14.44/7.26  tff(c_359, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_356])).
% 14.44/7.26  tff(c_363, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_145, c_86, c_359])).
% 14.44/7.26  tff(c_365, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_326])).
% 14.44/7.26  tff(c_364, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_326])).
% 14.44/7.26  tff(c_20, plain, (![A_13]: (k2_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_59])).
% 14.44/7.26  tff(c_90, plain, (![A_13]: (k2_relat_1(k6_partfun1(A_13))=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_20])).
% 14.44/7.26  tff(c_66, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_219])).
% 14.44/7.26  tff(c_3497, plain, (![A_270, C_271, B_272]: (k6_partfun1(A_270)=k5_relat_1(C_271, k2_funct_1(C_271)) | k1_xboole_0=B_272 | ~v2_funct_1(C_271) | k2_relset_1(A_270, B_272, C_271)!=B_272 | ~m1_subset_1(C_271, k1_zfmisc_1(k2_zfmisc_1(A_270, B_272))) | ~v1_funct_2(C_271, A_270, B_272) | ~v1_funct_1(C_271))), inference(cnfTransformation, [status(thm)], [f_193])).
% 14.44/7.26  tff(c_3501, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_3497])).
% 14.44/7.26  tff(c_3509, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_74, c_70, c_3501])).
% 14.44/7.26  tff(c_3510, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_66, c_3509])).
% 14.44/7.26  tff(c_12, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 14.44/7.26  tff(c_329, plain, (![B_96, A_97]: (k2_relat_1(k5_relat_1(B_96, A_97))=k2_relat_1(A_97) | ~r1_tarski(k1_relat_1(A_97), k2_relat_1(B_96)) | ~v1_relat_1(B_96) | ~v1_relat_1(A_97))), inference(cnfTransformation, [status(thm)], [f_55])).
% 14.44/7.26  tff(c_332, plain, (![A_97]: (k2_relat_1(k5_relat_1('#skF_3', A_97))=k2_relat_1(A_97) | ~r1_tarski(k1_relat_1(A_97), '#skF_2') | ~v1_relat_1('#skF_3') | ~v1_relat_1(A_97))), inference(superposition, [status(thm), theory('equality')], [c_256, c_329])).
% 14.44/7.26  tff(c_366, plain, (![A_98]: (k2_relat_1(k5_relat_1('#skF_3', A_98))=k2_relat_1(A_98) | ~r1_tarski(k1_relat_1(A_98), '#skF_2') | ~v1_relat_1(A_98))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_332])).
% 14.44/7.26  tff(c_377, plain, (![B_7]: (k2_relat_1(k5_relat_1('#skF_3', B_7))=k2_relat_1(B_7) | ~v4_relat_1(B_7, '#skF_2') | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_12, c_366])).
% 14.44/7.26  tff(c_3520, plain, (k2_relat_1(k6_partfun1('#skF_1'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3510, c_377])).
% 14.44/7.26  tff(c_3524, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_365, c_364, c_90, c_3520])).
% 14.44/7.26  tff(c_28, plain, (![A_16]: (k2_relat_1(k2_funct_1(A_16))=k1_relat_1(A_16) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_79])).
% 14.44/7.26  tff(c_3546, plain, (k1_relat_1('#skF_3')='#skF_1' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3524, c_28])).
% 14.44/7.26  tff(c_3565, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_145, c_86, c_70, c_3546])).
% 14.44/7.26  tff(c_3567, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3363, c_3565])).
% 14.44/7.26  tff(c_3569, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_1869])).
% 14.44/7.26  tff(c_221, plain, (![A_82]: (v4_relat_1(k2_funct_1(A_82), k2_relat_1(A_82)) | ~v1_relat_1(k2_funct_1(A_82)) | ~v2_funct_1(A_82) | ~v1_funct_1(A_82) | ~v1_relat_1(A_82))), inference(superposition, [status(thm), theory('equality')], [c_215, c_181])).
% 14.44/7.26  tff(c_3585, plain, (v4_relat_1(k2_funct_1('#skF_4'), k1_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3569, c_221])).
% 14.44/7.26  tff(c_3597, plain, (v4_relat_1(k2_funct_1('#skF_4'), k1_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_80, c_3585])).
% 14.44/7.26  tff(c_3634, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_3597])).
% 14.44/7.26  tff(c_26, plain, (![A_15]: (v2_funct_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.44/7.26  tff(c_89, plain, (![A_15]: (v2_funct_1(k6_partfun1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_26])).
% 14.44/7.26  tff(c_6220, plain, (![A_409, C_408, D_407, B_406, E_405]: (k1_xboole_0=C_408 | v2_funct_1(E_405) | k2_relset_1(A_409, B_406, D_407)!=B_406 | ~v2_funct_1(k1_partfun1(A_409, B_406, B_406, C_408, D_407, E_405)) | ~m1_subset_1(E_405, k1_zfmisc_1(k2_zfmisc_1(B_406, C_408))) | ~v1_funct_2(E_405, B_406, C_408) | ~v1_funct_1(E_405) | ~m1_subset_1(D_407, k1_zfmisc_1(k2_zfmisc_1(A_409, B_406))) | ~v1_funct_2(D_407, A_409, B_406) | ~v1_funct_1(D_407))), inference(cnfTransformation, [status(thm)], [f_177])).
% 14.44/7.26  tff(c_6224, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1575, c_6220])).
% 14.44/7.26  tff(c_6229, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_80, c_78, c_76, c_89, c_74, c_6224])).
% 14.44/7.26  tff(c_6231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3634, c_68, c_6229])).
% 14.44/7.26  tff(c_6232, plain, (~v1_relat_1(k2_funct_1('#skF_4')) | v4_relat_1(k2_funct_1('#skF_4'), k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_3597])).
% 14.44/7.26  tff(c_6234, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_6232])).
% 14.44/7.26  tff(c_6237, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_6234])).
% 14.44/7.26  tff(c_6241, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_148, c_80, c_6237])).
% 14.44/7.26  tff(c_6243, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_6232])).
% 14.44/7.26  tff(c_22, plain, (![A_14]: (v1_funct_1(k2_funct_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_67])).
% 14.44/7.26  tff(c_6233, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_3597])).
% 14.44/7.26  tff(c_8322, plain, (![A_520, C_521, B_522]: (k6_partfun1(A_520)=k5_relat_1(C_521, k2_funct_1(C_521)) | k1_xboole_0=B_522 | ~v2_funct_1(C_521) | k2_relset_1(A_520, B_522, C_521)!=B_522 | ~m1_subset_1(C_521, k1_zfmisc_1(k2_zfmisc_1(A_520, B_522))) | ~v1_funct_2(C_521, A_520, B_522) | ~v1_funct_1(C_521))), inference(cnfTransformation, [status(thm)], [f_193])).
% 14.44/7.26  tff(c_8326, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_8322])).
% 14.44/7.26  tff(c_8334, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_74, c_70, c_8326])).
% 14.44/7.26  tff(c_8335, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_66, c_8334])).
% 14.44/7.26  tff(c_8343, plain, (k2_relat_1(k6_partfun1('#skF_1'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_8335, c_377])).
% 14.44/7.26  tff(c_8347, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_365, c_364, c_90, c_8343])).
% 14.44/7.26  tff(c_8366, plain, (k1_relat_1('#skF_3')='#skF_1' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8347, c_28])).
% 14.44/7.26  tff(c_8383, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_145, c_86, c_70, c_8366])).
% 14.44/7.26  tff(c_8401, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8383, c_3569])).
% 14.44/7.26  tff(c_30, plain, (![A_16]: (k1_relat_1(k2_funct_1(A_16))=k2_relat_1(A_16) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_79])).
% 14.44/7.26  tff(c_6242, plain, (v4_relat_1(k2_funct_1('#skF_4'), k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_6232])).
% 14.44/7.26  tff(c_157, plain, (![B_71, A_72]: (r1_tarski(k1_relat_1(B_71), A_72) | ~v4_relat_1(B_71, A_72) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_44])).
% 14.44/7.26  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.44/7.26  tff(c_276, plain, (![B_91, A_92]: (k1_relat_1(B_91)=A_92 | ~r1_tarski(A_92, k1_relat_1(B_91)) | ~v4_relat_1(B_91, A_92) | ~v1_relat_1(B_91))), inference(resolution, [status(thm)], [c_157, c_2])).
% 14.44/7.26  tff(c_291, plain, (![B_91, B_7]: (k1_relat_1(B_91)=k1_relat_1(B_7) | ~v4_relat_1(B_91, k1_relat_1(B_7)) | ~v1_relat_1(B_91) | ~v4_relat_1(B_7, k1_relat_1(B_91)) | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_12, c_276])).
% 14.44/7.26  tff(c_6250, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v4_relat_1('#skF_3', k1_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6242, c_291])).
% 14.44/7.26  tff(c_6253, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_3') | ~v4_relat_1('#skF_3', k1_relat_1(k2_funct_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_6243, c_6250])).
% 14.44/7.26  tff(c_6254, plain, (~v4_relat_1('#skF_3', k1_relat_1(k2_funct_1('#skF_4')))), inference(splitLeft, [status(thm)], [c_6253])).
% 14.44/7.26  tff(c_6257, plain, (~v4_relat_1('#skF_3', k2_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_30, c_6254])).
% 14.44/7.26  tff(c_6259, plain, (~v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_80, c_6233, c_3569, c_6257])).
% 14.44/7.26  tff(c_6276, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_181, c_6259])).
% 14.44/7.26  tff(c_6280, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_145, c_6276])).
% 14.44/7.26  tff(c_6281, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_6253])).
% 14.44/7.26  tff(c_8396, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8383, c_6281])).
% 14.44/7.26  tff(c_3570, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3569, c_257])).
% 14.44/7.26  tff(c_8328, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_8322])).
% 14.44/7.26  tff(c_8338, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_3570, c_6233, c_8328])).
% 14.44/7.26  tff(c_8339, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_68, c_8338])).
% 14.44/7.26  tff(c_8447, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8383, c_8339])).
% 14.44/7.26  tff(c_351, plain, (![B_96, B_7]: (k2_relat_1(k5_relat_1(B_96, B_7))=k2_relat_1(B_7) | ~v1_relat_1(B_96) | ~v4_relat_1(B_7, k2_relat_1(B_96)) | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_12, c_329])).
% 14.44/7.26  tff(c_3579, plain, (![B_7]: (k2_relat_1(k5_relat_1('#skF_4', B_7))=k2_relat_1(B_7) | ~v1_relat_1('#skF_4') | ~v4_relat_1(B_7, k1_relat_1('#skF_3')) | ~v1_relat_1(B_7))), inference(superposition, [status(thm), theory('equality')], [c_3569, c_351])).
% 14.44/7.26  tff(c_6343, plain, (![B_416]: (k2_relat_1(k5_relat_1('#skF_4', B_416))=k2_relat_1(B_416) | ~v4_relat_1(B_416, k1_relat_1('#skF_3')) | ~v1_relat_1(B_416))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_3579])).
% 14.44/7.26  tff(c_6349, plain, (k2_relat_1(k5_relat_1('#skF_4', k2_funct_1('#skF_4')))=k2_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_6242, c_6343])).
% 14.44/7.26  tff(c_6371, plain, (k2_relat_1(k5_relat_1('#skF_4', k2_funct_1('#skF_4')))=k2_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6243, c_6349])).
% 14.44/7.26  tff(c_8448, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k2_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8447, c_6371])).
% 14.44/7.26  tff(c_8449, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_8448])).
% 14.44/7.26  tff(c_8519, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8449, c_28])).
% 14.44/7.26  tff(c_8536, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_148, c_80, c_6233, c_8519])).
% 14.44/7.26  tff(c_16519, plain, (![A_751, B_752]: (k2_funct_1(k2_funct_1(A_751))=B_752 | k5_relat_1(B_752, k2_funct_1(A_751))!=k6_partfun1(k1_relat_1(A_751)) | k2_relat_1(B_752)!=k1_relat_1(k2_funct_1(A_751)) | ~v2_funct_1(k2_funct_1(A_751)) | ~v1_funct_1(B_752) | ~v1_relat_1(B_752) | ~v1_funct_1(k2_funct_1(A_751)) | ~v1_relat_1(k2_funct_1(A_751)) | ~v2_funct_1(A_751) | ~v1_funct_1(A_751) | ~v1_relat_1(A_751))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1800])).
% 14.44/7.26  tff(c_16521, plain, (k2_funct_1(k2_funct_1('#skF_4'))='#skF_4' | k6_partfun1(k1_relat_1('#skF_4'))!=k6_partfun1('#skF_2') | k1_relat_1(k2_funct_1('#skF_4'))!=k2_relat_1('#skF_4') | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8447, c_16519])).
% 14.44/7.26  tff(c_16525, plain, (k2_funct_1(k2_funct_1('#skF_4'))='#skF_4' | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_80, c_6233, c_6243, c_148, c_80, c_8401, c_8396, c_8536, c_16521])).
% 14.44/7.26  tff(c_16528, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_16525])).
% 14.44/7.26  tff(c_16531, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_16528])).
% 14.44/7.26  tff(c_16535, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_148, c_80, c_16531])).
% 14.44/7.26  tff(c_16537, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_16525])).
% 14.44/7.26  tff(c_88, plain, (![A_17, B_19]: (k2_funct_1(A_17)=B_19 | k6_partfun1(k2_relat_1(A_17))!=k5_relat_1(B_19, A_17) | k2_relat_1(B_19)!=k1_relat_1(A_17) | ~v2_funct_1(A_17) | ~v1_funct_1(B_19) | ~v1_relat_1(B_19) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_32])).
% 14.44/7.26  tff(c_8456, plain, (![B_19]: (k2_funct_1('#skF_4')=B_19 | k5_relat_1(B_19, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_19)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_19) | ~v1_relat_1(B_19) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8401, c_88])).
% 14.44/7.26  tff(c_8472, plain, (![B_19]: (k2_funct_1('#skF_4')=B_19 | k5_relat_1(B_19, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_19)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_19) | ~v1_relat_1(B_19))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_80, c_6233, c_8456])).
% 14.44/7.26  tff(c_24323, plain, (![B_880]: (k2_funct_1('#skF_4')=B_880 | k5_relat_1(B_880, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_880)!='#skF_2' | ~v1_funct_1(B_880) | ~v1_relat_1(B_880))), inference(demodulation, [status(thm), theory('equality')], [c_8536, c_8472])).
% 14.44/7.26  tff(c_24551, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_145, c_24323])).
% 14.44/7.26  tff(c_24759, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_256, c_10320, c_24551])).
% 14.44/7.26  tff(c_16536, plain, (~v2_funct_1(k2_funct_1('#skF_4')) | k2_funct_1(k2_funct_1('#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_16525])).
% 14.44/7.26  tff(c_16539, plain, (~v2_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_16536])).
% 14.44/7.26  tff(c_24765, plain, (~v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24759, c_16539])).
% 14.44/7.26  tff(c_24784, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_24765])).
% 14.44/7.26  tff(c_24786, plain, (v2_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_16536])).
% 14.44/7.26  tff(c_24785, plain, (k2_funct_1(k2_funct_1('#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_16536])).
% 14.44/7.26  tff(c_1820, plain, (![A_16, B_182]: (k2_funct_1(k2_funct_1(A_16))=B_182 | k5_relat_1(B_182, k2_funct_1(A_16))!=k6_partfun1(k1_relat_1(A_16)) | k2_relat_1(B_182)!=k1_relat_1(k2_funct_1(A_16)) | ~v2_funct_1(k2_funct_1(A_16)) | ~v1_funct_1(B_182) | ~v1_relat_1(B_182) | ~v1_funct_1(k2_funct_1(A_16)) | ~v1_relat_1(k2_funct_1(A_16)) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1800])).
% 14.44/7.26  tff(c_24789, plain, (![B_182]: (k2_funct_1(k2_funct_1(k2_funct_1('#skF_4')))=B_182 | k6_partfun1(k1_relat_1(k2_funct_1('#skF_4')))!=k5_relat_1(B_182, '#skF_4') | k2_relat_1(B_182)!=k1_relat_1(k2_funct_1(k2_funct_1('#skF_4'))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(B_182) | ~v1_relat_1(B_182) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_4'))) | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_24785, c_1820])).
% 14.44/7.26  tff(c_27078, plain, (![B_942]: (k2_funct_1('#skF_4')=B_942 | k5_relat_1(B_942, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_942)!='#skF_2' | ~v1_funct_1(B_942) | ~v1_relat_1(B_942))), inference(demodulation, [status(thm), theory('equality')], [c_6243, c_16537, c_24786, c_148, c_24785, c_80, c_24785, c_6233, c_24785, c_8536, c_24785, c_8396, c_24785, c_24789])).
% 14.44/7.26  tff(c_27183, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_145, c_27078])).
% 14.44/7.26  tff(c_27289, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_256, c_10320, c_27183])).
% 14.44/7.26  tff(c_27296, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_27289, c_24785])).
% 14.44/7.26  tff(c_27315, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_27296])).
% 14.44/7.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.44/7.26  
% 14.44/7.26  Inference rules
% 14.44/7.26  ----------------------
% 14.44/7.26  #Ref     : 0
% 14.44/7.26  #Sup     : 5682
% 14.44/7.26  #Fact    : 0
% 14.44/7.26  #Define  : 0
% 14.44/7.26  #Split   : 101
% 14.44/7.26  #Chain   : 0
% 14.44/7.26  #Close   : 0
% 14.44/7.26  
% 14.44/7.26  Ordering : KBO
% 14.44/7.26  
% 14.44/7.26  Simplification rules
% 14.44/7.26  ----------------------
% 14.44/7.26  #Subsume      : 618
% 14.44/7.26  #Demod        : 11336
% 14.44/7.26  #Tautology    : 1883
% 14.44/7.26  #SimpNegUnit  : 449
% 14.44/7.26  #BackRed      : 170
% 14.44/7.26  
% 14.44/7.26  #Partial instantiations: 0
% 14.44/7.26  #Strategies tried      : 1
% 14.44/7.26  
% 14.44/7.26  Timing (in seconds)
% 14.44/7.26  ----------------------
% 14.51/7.27  Preprocessing        : 0.38
% 14.51/7.27  Parsing              : 0.20
% 14.51/7.27  CNF conversion       : 0.03
% 14.51/7.27  Main loop            : 5.99
% 14.51/7.27  Inferencing          : 1.36
% 14.51/7.27  Reduction            : 3.10
% 14.51/7.27  Demodulation         : 2.58
% 14.51/7.27  BG Simplification    : 0.12
% 14.51/7.27  Subsumption          : 1.14
% 14.51/7.27  Abstraction          : 0.18
% 14.51/7.27  MUC search           : 0.00
% 14.51/7.27  Cooper               : 0.00
% 14.51/7.27  Total                : 6.46
% 14.51/7.27  Index Insertion      : 0.00
% 14.51/7.27  Index Deletion       : 0.00
% 14.51/7.27  Index Matching       : 0.00
% 14.51/7.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
