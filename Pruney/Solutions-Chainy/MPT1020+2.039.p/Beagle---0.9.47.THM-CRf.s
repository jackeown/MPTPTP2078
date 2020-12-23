%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:56 EST 2020

% Result     : Theorem 4.46s
% Output     : CNFRefutation 4.54s
% Verified   : 
% Statistics : Number of formulae       :  156 (2047 expanded)
%              Number of leaves         :   40 ( 676 expanded)
%              Depth                    :   16
%              Number of atoms          :  304 (6060 expanded)
%              Number of equality atoms :   79 (1511 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_180,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & v3_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,C),k6_partfun1(A))
             => r2_relset_1(A,A,C,k2_funct_2(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_158,axiom,(
    ! [A,B,C] :
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

tff(f_112,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_46,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_107,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_122,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_107])).

tff(c_66,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_123,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_107])).

tff(c_606,plain,(
    ! [A_102,B_103,D_104] :
      ( r2_relset_1(A_102,B_103,D_104,D_104)
      | ~ m1_subset_1(D_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_617,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_606])).

tff(c_180,plain,(
    ! [C_48,B_49,A_50] :
      ( v5_relat_1(C_48,B_49)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_50,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_196,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_180])).

tff(c_253,plain,(
    ! [B_62,A_63] :
      ( k2_relat_1(B_62) = A_63
      | ~ v2_funct_2(B_62,A_63)
      | ~ v5_relat_1(B_62,A_63)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_262,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_196,c_253])).

tff(c_274,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_262])).

tff(c_278,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_274])).

tff(c_72,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_68,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_466,plain,(
    ! [C_87,B_88,A_89] :
      ( v2_funct_2(C_87,B_88)
      | ~ v3_funct_2(C_87,A_89,B_88)
      | ~ v1_funct_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_89,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_478,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_466])).

tff(c_488,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_478])).

tff(c_490,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_278,c_488])).

tff(c_491,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_274])).

tff(c_2,plain,(
    ! [A_1] :
      ( k2_relat_1(A_1) != k1_xboole_0
      | k1_xboole_0 = A_1
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_138,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_123,c_2])).

tff(c_172,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_493,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_491,c_172])).

tff(c_70,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_64,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_62,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_619,plain,(
    ! [A_105,B_106,C_107] :
      ( k2_relset_1(A_105,B_106,C_107) = k2_relat_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_631,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_619])).

tff(c_637,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_491,c_631])).

tff(c_672,plain,(
    ! [C_110,A_111,B_112] :
      ( v2_funct_1(C_110)
      | ~ v3_funct_2(C_110,A_111,B_112)
      | ~ v1_funct_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_684,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_672])).

tff(c_692,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_684])).

tff(c_56,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_926,plain,(
    ! [C_144,D_145,B_146,A_147] :
      ( k2_funct_1(C_144) = D_145
      | k1_xboole_0 = B_146
      | k1_xboole_0 = A_147
      | ~ v2_funct_1(C_144)
      | ~ r2_relset_1(A_147,A_147,k1_partfun1(A_147,B_146,B_146,A_147,C_144,D_145),k6_partfun1(A_147))
      | k2_relset_1(A_147,B_146,C_144) != B_146
      | ~ m1_subset_1(D_145,k1_zfmisc_1(k2_zfmisc_1(B_146,A_147)))
      | ~ v1_funct_2(D_145,B_146,A_147)
      | ~ v1_funct_1(D_145)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_147,B_146)))
      | ~ v1_funct_2(C_144,A_147,B_146)
      | ~ v1_funct_1(C_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_929,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_926])).

tff(c_935,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_62,c_58,c_637,c_692,c_929])).

tff(c_936,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_493,c_935])).

tff(c_804,plain,(
    ! [A_128,B_129] :
      ( k2_funct_2(A_128,B_129) = k2_funct_1(B_129)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(k2_zfmisc_1(A_128,A_128)))
      | ~ v3_funct_2(B_129,A_128,A_128)
      | ~ v1_funct_2(B_129,A_128,A_128)
      | ~ v1_funct_1(B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_816,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_804])).

tff(c_824,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_816])).

tff(c_54,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_839,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_824,c_54])).

tff(c_938,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_936,c_839])).

tff(c_942,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_617,c_938])).

tff(c_943,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_944,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_958,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_943,c_944])).

tff(c_989,plain,(
    ! [C_148,B_149,A_150] :
      ( v5_relat_1(C_148,B_149)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_150,B_149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1001,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_989])).

tff(c_1122,plain,(
    ! [B_165,A_166] :
      ( k2_relat_1(B_165) = A_166
      | ~ v2_funct_2(B_165,A_166)
      | ~ v5_relat_1(B_165,A_166)
      | ~ v1_relat_1(B_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1131,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1001,c_1122])).

tff(c_1143,plain,
    ( '#skF_2' = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_958,c_1131])).

tff(c_1147,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1143])).

tff(c_1366,plain,(
    ! [C_193,B_194,A_195] :
      ( v2_funct_2(C_193,B_194)
      | ~ v3_funct_2(C_193,A_195,B_194)
      | ~ v1_funct_1(C_193)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(A_195,B_194))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1378,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_1366])).

tff(c_1388,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_1378])).

tff(c_1390,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1147,c_1388])).

tff(c_1391,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1143])).

tff(c_130,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_122,c_2])).

tff(c_963,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_943,c_943,c_130])).

tff(c_964,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_963])).

tff(c_1403,plain,(
    k2_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1391,c_964])).

tff(c_1000,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_989])).

tff(c_1134,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1000,c_1122])).

tff(c_1146,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_1134])).

tff(c_1544,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1403,c_1146])).

tff(c_60,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_1555,plain,(
    ! [C_206,B_207,A_208] :
      ( v2_funct_2(C_206,B_207)
      | ~ v3_funct_2(C_206,A_208,B_207)
      | ~ v1_funct_1(C_206)
      | ~ m1_subset_1(C_206,k1_zfmisc_1(k2_zfmisc_1(A_208,B_207))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1564,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_1555])).

tff(c_1571,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_1564])).

tff(c_1573,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1544,c_1571])).

tff(c_1574,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_963])).

tff(c_1575,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_963])).

tff(c_1598,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1574,c_1575])).

tff(c_1676,plain,(
    ! [C_215,B_216,A_217] :
      ( v5_relat_1(C_215,B_216)
      | ~ m1_subset_1(C_215,k1_zfmisc_1(k2_zfmisc_1(A_217,B_216))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1688,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_1676])).

tff(c_1746,plain,(
    ! [B_229,A_230] :
      ( k2_relat_1(B_229) = A_230
      | ~ v2_funct_2(B_229,A_230)
      | ~ v5_relat_1(B_229,A_230)
      | ~ v1_relat_1(B_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1755,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1688,c_1746])).

tff(c_1764,plain,
    ( '#skF_3' = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_1598,c_1755])).

tff(c_1765,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1764])).

tff(c_1844,plain,(
    ! [C_241,B_242,A_243] :
      ( v2_funct_2(C_241,B_242)
      | ~ v3_funct_2(C_241,A_243,B_242)
      | ~ v1_funct_1(C_241)
      | ~ m1_subset_1(C_241,k1_zfmisc_1(k2_zfmisc_1(A_243,B_242))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1853,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_1844])).

tff(c_1860,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_1853])).

tff(c_1862,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1765,c_1860])).

tff(c_1863,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1764])).

tff(c_1727,plain,(
    ! [A_225,B_226,D_227] :
      ( r2_relset_1(A_225,B_226,D_227,D_227)
      | ~ m1_subset_1(D_227,k1_zfmisc_1(k2_zfmisc_1(A_225,B_226))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1736,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_1727])).

tff(c_1866,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1863,c_1863,c_1736])).

tff(c_1885,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1863,c_122])).

tff(c_1889,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1863,c_64])).

tff(c_1888,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1863,c_60])).

tff(c_1886,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1863,c_58])).

tff(c_2000,plain,(
    ! [C_248,A_249,B_250] :
      ( v2_funct_1(C_248)
      | ~ v3_funct_2(C_248,A_249,B_250)
      | ~ v1_funct_1(C_248)
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(A_249,B_250))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2003,plain,
    ( v2_funct_1('#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1886,c_2000])).

tff(c_2009,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1889,c_1888,c_2003])).

tff(c_1882,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1863,c_1863,c_1598])).

tff(c_16,plain,(
    ! [A_3] :
      ( k1_relat_1(k2_funct_1(A_3)) = k2_relat_1(A_3)
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1577,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1574,c_943])).

tff(c_1883,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1863,c_1577])).

tff(c_162,plain,(
    ! [A_46] :
      ( v1_relat_1(k2_funct_1(A_46))
      | ~ v2_funct_1(A_46)
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_relat_1(A_1) != k1_xboole_0
      | k1_xboole_0 = A_1
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_170,plain,(
    ! [A_46] :
      ( k1_relat_1(k2_funct_1(A_46)) != k1_xboole_0
      | k2_funct_1(A_46) = k1_xboole_0
      | ~ v2_funct_1(A_46)
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(resolution,[status(thm)],[c_162,c_4])).

tff(c_2114,plain,(
    ! [A_266] :
      ( k1_relat_1(k2_funct_1(A_266)) != '#skF_1'
      | k2_funct_1(A_266) = '#skF_1'
      | ~ v2_funct_1(A_266)
      | ~ v1_funct_1(A_266)
      | ~ v1_relat_1(A_266) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1883,c_1883,c_170])).

tff(c_2151,plain,(
    ! [A_271] :
      ( k2_relat_1(A_271) != '#skF_1'
      | k2_funct_1(A_271) = '#skF_1'
      | ~ v2_funct_1(A_271)
      | ~ v1_funct_1(A_271)
      | ~ v1_relat_1(A_271)
      | ~ v2_funct_1(A_271)
      | ~ v1_funct_1(A_271)
      | ~ v1_relat_1(A_271) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2114])).

tff(c_2153,plain,
    ( k2_relat_1('#skF_1') != '#skF_1'
    | k2_funct_1('#skF_1') = '#skF_1'
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2009,c_2151])).

tff(c_2158,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1885,c_1889,c_2009,c_1882,c_2153])).

tff(c_1887,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1863,c_62])).

tff(c_2124,plain,(
    ! [A_268,B_269] :
      ( k2_funct_2(A_268,B_269) = k2_funct_1(B_269)
      | ~ m1_subset_1(B_269,k1_zfmisc_1(k2_zfmisc_1(A_268,A_268)))
      | ~ v3_funct_2(B_269,A_268,A_268)
      | ~ v1_funct_2(B_269,A_268,A_268)
      | ~ v1_funct_1(B_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2127,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1886,c_2124])).

tff(c_2133,plain,(
    k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1889,c_1887,c_1888,c_2127])).

tff(c_1580,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1574,c_54])).

tff(c_1881,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1863,c_1863,c_1580])).

tff(c_2135,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2133,c_1881])).

tff(c_2160,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2158,c_2135])).

tff(c_2164,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1866,c_2160])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:46:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.46/1.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.54/1.76  
% 4.54/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.54/1.77  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.54/1.77  
% 4.54/1.77  %Foreground sorts:
% 4.54/1.77  
% 4.54/1.77  
% 4.54/1.77  %Background operators:
% 4.54/1.77  
% 4.54/1.77  
% 4.54/1.77  %Foreground operators:
% 4.54/1.77  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.54/1.77  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.54/1.77  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.54/1.77  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.54/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.54/1.77  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.54/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.54/1.77  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 4.54/1.77  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.54/1.77  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.54/1.77  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.54/1.77  tff('#skF_2', type, '#skF_2': $i).
% 4.54/1.77  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.54/1.77  tff('#skF_3', type, '#skF_3': $i).
% 4.54/1.77  tff('#skF_1', type, '#skF_1': $i).
% 4.54/1.77  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.54/1.77  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.54/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.54/1.77  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.54/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.54/1.77  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.54/1.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.54/1.77  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.54/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.54/1.77  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.54/1.77  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 4.54/1.77  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.54/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.54/1.77  
% 4.54/1.79  tff(f_180, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_2)).
% 4.54/1.79  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.54/1.79  tff(f_78, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.54/1.79  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.54/1.79  tff(f_98, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 4.54/1.79  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 4.54/1.79  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 4.54/1.79  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.54/1.79  tff(f_158, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 4.54/1.79  tff(f_112, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 4.54/1.79  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 4.54/1.79  tff(f_46, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 4.54/1.79  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.54/1.79  tff(c_107, plain, (![C_42, A_43, B_44]: (v1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.54/1.79  tff(c_122, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_107])).
% 4.54/1.79  tff(c_66, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.54/1.79  tff(c_123, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_107])).
% 4.54/1.79  tff(c_606, plain, (![A_102, B_103, D_104]: (r2_relset_1(A_102, B_103, D_104, D_104) | ~m1_subset_1(D_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.54/1.79  tff(c_617, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_606])).
% 4.54/1.79  tff(c_180, plain, (![C_48, B_49, A_50]: (v5_relat_1(C_48, B_49) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_50, B_49))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.54/1.79  tff(c_196, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_180])).
% 4.54/1.79  tff(c_253, plain, (![B_62, A_63]: (k2_relat_1(B_62)=A_63 | ~v2_funct_2(B_62, A_63) | ~v5_relat_1(B_62, A_63) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.54/1.79  tff(c_262, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_196, c_253])).
% 4.54/1.79  tff(c_274, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_262])).
% 4.54/1.79  tff(c_278, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_274])).
% 4.54/1.79  tff(c_72, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.54/1.79  tff(c_68, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.54/1.79  tff(c_466, plain, (![C_87, B_88, A_89]: (v2_funct_2(C_87, B_88) | ~v3_funct_2(C_87, A_89, B_88) | ~v1_funct_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_89, B_88))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.54/1.79  tff(c_478, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_466])).
% 4.54/1.79  tff(c_488, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_478])).
% 4.54/1.79  tff(c_490, plain, $false, inference(negUnitSimplification, [status(thm)], [c_278, c_488])).
% 4.54/1.79  tff(c_491, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_274])).
% 4.54/1.79  tff(c_2, plain, (![A_1]: (k2_relat_1(A_1)!=k1_xboole_0 | k1_xboole_0=A_1 | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.54/1.79  tff(c_138, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_123, c_2])).
% 4.54/1.79  tff(c_172, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_138])).
% 4.54/1.79  tff(c_493, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_491, c_172])).
% 4.54/1.79  tff(c_70, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.54/1.79  tff(c_64, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.54/1.79  tff(c_62, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.54/1.79  tff(c_619, plain, (![A_105, B_106, C_107]: (k2_relset_1(A_105, B_106, C_107)=k2_relat_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.54/1.79  tff(c_631, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_619])).
% 4.54/1.79  tff(c_637, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_491, c_631])).
% 4.54/1.79  tff(c_672, plain, (![C_110, A_111, B_112]: (v2_funct_1(C_110) | ~v3_funct_2(C_110, A_111, B_112) | ~v1_funct_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.54/1.79  tff(c_684, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_672])).
% 4.54/1.79  tff(c_692, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_684])).
% 4.54/1.79  tff(c_56, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.54/1.79  tff(c_926, plain, (![C_144, D_145, B_146, A_147]: (k2_funct_1(C_144)=D_145 | k1_xboole_0=B_146 | k1_xboole_0=A_147 | ~v2_funct_1(C_144) | ~r2_relset_1(A_147, A_147, k1_partfun1(A_147, B_146, B_146, A_147, C_144, D_145), k6_partfun1(A_147)) | k2_relset_1(A_147, B_146, C_144)!=B_146 | ~m1_subset_1(D_145, k1_zfmisc_1(k2_zfmisc_1(B_146, A_147))) | ~v1_funct_2(D_145, B_146, A_147) | ~v1_funct_1(D_145) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_147, B_146))) | ~v1_funct_2(C_144, A_147, B_146) | ~v1_funct_1(C_144))), inference(cnfTransformation, [status(thm)], [f_158])).
% 4.54/1.79  tff(c_929, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_926])).
% 4.54/1.79  tff(c_935, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_62, c_58, c_637, c_692, c_929])).
% 4.54/1.79  tff(c_936, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_493, c_935])).
% 4.54/1.79  tff(c_804, plain, (![A_128, B_129]: (k2_funct_2(A_128, B_129)=k2_funct_1(B_129) | ~m1_subset_1(B_129, k1_zfmisc_1(k2_zfmisc_1(A_128, A_128))) | ~v3_funct_2(B_129, A_128, A_128) | ~v1_funct_2(B_129, A_128, A_128) | ~v1_funct_1(B_129))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.54/1.79  tff(c_816, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_804])).
% 4.54/1.79  tff(c_824, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_816])).
% 4.54/1.79  tff(c_54, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.54/1.79  tff(c_839, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_824, c_54])).
% 4.54/1.79  tff(c_938, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_936, c_839])).
% 4.54/1.79  tff(c_942, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_617, c_938])).
% 4.54/1.79  tff(c_943, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_138])).
% 4.54/1.79  tff(c_944, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_138])).
% 4.54/1.79  tff(c_958, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_943, c_944])).
% 4.54/1.79  tff(c_989, plain, (![C_148, B_149, A_150]: (v5_relat_1(C_148, B_149) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_150, B_149))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.54/1.79  tff(c_1001, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_989])).
% 4.54/1.79  tff(c_1122, plain, (![B_165, A_166]: (k2_relat_1(B_165)=A_166 | ~v2_funct_2(B_165, A_166) | ~v5_relat_1(B_165, A_166) | ~v1_relat_1(B_165))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.54/1.79  tff(c_1131, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1001, c_1122])).
% 4.54/1.79  tff(c_1143, plain, ('#skF_2'='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_958, c_1131])).
% 4.54/1.79  tff(c_1147, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_1143])).
% 4.54/1.79  tff(c_1366, plain, (![C_193, B_194, A_195]: (v2_funct_2(C_193, B_194) | ~v3_funct_2(C_193, A_195, B_194) | ~v1_funct_1(C_193) | ~m1_subset_1(C_193, k1_zfmisc_1(k2_zfmisc_1(A_195, B_194))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.54/1.79  tff(c_1378, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_1366])).
% 4.54/1.79  tff(c_1388, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_1378])).
% 4.54/1.79  tff(c_1390, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1147, c_1388])).
% 4.54/1.79  tff(c_1391, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_1143])).
% 4.54/1.79  tff(c_130, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_122, c_2])).
% 4.54/1.79  tff(c_963, plain, (k2_relat_1('#skF_3')!='#skF_2' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_943, c_943, c_130])).
% 4.54/1.79  tff(c_964, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_963])).
% 4.54/1.79  tff(c_1403, plain, (k2_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1391, c_964])).
% 4.54/1.79  tff(c_1000, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_989])).
% 4.54/1.79  tff(c_1134, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1000, c_1122])).
% 4.54/1.79  tff(c_1146, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_1134])).
% 4.54/1.79  tff(c_1544, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1403, c_1146])).
% 4.54/1.79  tff(c_60, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_180])).
% 4.54/1.79  tff(c_1555, plain, (![C_206, B_207, A_208]: (v2_funct_2(C_206, B_207) | ~v3_funct_2(C_206, A_208, B_207) | ~v1_funct_1(C_206) | ~m1_subset_1(C_206, k1_zfmisc_1(k2_zfmisc_1(A_208, B_207))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.54/1.79  tff(c_1564, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_1555])).
% 4.54/1.79  tff(c_1571, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_1564])).
% 4.54/1.79  tff(c_1573, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1544, c_1571])).
% 4.54/1.79  tff(c_1574, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_963])).
% 4.54/1.79  tff(c_1575, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_963])).
% 4.54/1.79  tff(c_1598, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1574, c_1575])).
% 4.54/1.79  tff(c_1676, plain, (![C_215, B_216, A_217]: (v5_relat_1(C_215, B_216) | ~m1_subset_1(C_215, k1_zfmisc_1(k2_zfmisc_1(A_217, B_216))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.54/1.79  tff(c_1688, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_1676])).
% 4.54/1.79  tff(c_1746, plain, (![B_229, A_230]: (k2_relat_1(B_229)=A_230 | ~v2_funct_2(B_229, A_230) | ~v5_relat_1(B_229, A_230) | ~v1_relat_1(B_229))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.54/1.79  tff(c_1755, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1688, c_1746])).
% 4.54/1.79  tff(c_1764, plain, ('#skF_3'='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_1598, c_1755])).
% 4.54/1.79  tff(c_1765, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_1764])).
% 4.54/1.79  tff(c_1844, plain, (![C_241, B_242, A_243]: (v2_funct_2(C_241, B_242) | ~v3_funct_2(C_241, A_243, B_242) | ~v1_funct_1(C_241) | ~m1_subset_1(C_241, k1_zfmisc_1(k2_zfmisc_1(A_243, B_242))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.54/1.79  tff(c_1853, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_1844])).
% 4.54/1.79  tff(c_1860, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_1853])).
% 4.54/1.79  tff(c_1862, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1765, c_1860])).
% 4.54/1.79  tff(c_1863, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_1764])).
% 4.54/1.79  tff(c_1727, plain, (![A_225, B_226, D_227]: (r2_relset_1(A_225, B_226, D_227, D_227) | ~m1_subset_1(D_227, k1_zfmisc_1(k2_zfmisc_1(A_225, B_226))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.54/1.79  tff(c_1736, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_1727])).
% 4.54/1.79  tff(c_1866, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1863, c_1863, c_1736])).
% 4.54/1.79  tff(c_1885, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1863, c_122])).
% 4.54/1.79  tff(c_1889, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1863, c_64])).
% 4.54/1.79  tff(c_1888, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1863, c_60])).
% 4.54/1.79  tff(c_1886, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1863, c_58])).
% 4.54/1.79  tff(c_2000, plain, (![C_248, A_249, B_250]: (v2_funct_1(C_248) | ~v3_funct_2(C_248, A_249, B_250) | ~v1_funct_1(C_248) | ~m1_subset_1(C_248, k1_zfmisc_1(k2_zfmisc_1(A_249, B_250))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.54/1.79  tff(c_2003, plain, (v2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_1886, c_2000])).
% 4.54/1.79  tff(c_2009, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1889, c_1888, c_2003])).
% 4.54/1.79  tff(c_1882, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1863, c_1863, c_1598])).
% 4.54/1.79  tff(c_16, plain, (![A_3]: (k1_relat_1(k2_funct_1(A_3))=k2_relat_1(A_3) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.54/1.79  tff(c_1577, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1574, c_943])).
% 4.54/1.79  tff(c_1883, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1863, c_1577])).
% 4.54/1.79  tff(c_162, plain, (![A_46]: (v1_relat_1(k2_funct_1(A_46)) | ~v2_funct_1(A_46) | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.54/1.79  tff(c_4, plain, (![A_1]: (k1_relat_1(A_1)!=k1_xboole_0 | k1_xboole_0=A_1 | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.54/1.79  tff(c_170, plain, (![A_46]: (k1_relat_1(k2_funct_1(A_46))!=k1_xboole_0 | k2_funct_1(A_46)=k1_xboole_0 | ~v2_funct_1(A_46) | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(resolution, [status(thm)], [c_162, c_4])).
% 4.54/1.79  tff(c_2114, plain, (![A_266]: (k1_relat_1(k2_funct_1(A_266))!='#skF_1' | k2_funct_1(A_266)='#skF_1' | ~v2_funct_1(A_266) | ~v1_funct_1(A_266) | ~v1_relat_1(A_266))), inference(demodulation, [status(thm), theory('equality')], [c_1883, c_1883, c_170])).
% 4.54/1.79  tff(c_2151, plain, (![A_271]: (k2_relat_1(A_271)!='#skF_1' | k2_funct_1(A_271)='#skF_1' | ~v2_funct_1(A_271) | ~v1_funct_1(A_271) | ~v1_relat_1(A_271) | ~v2_funct_1(A_271) | ~v1_funct_1(A_271) | ~v1_relat_1(A_271))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2114])).
% 4.54/1.79  tff(c_2153, plain, (k2_relat_1('#skF_1')!='#skF_1' | k2_funct_1('#skF_1')='#skF_1' | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_2009, c_2151])).
% 4.54/1.79  tff(c_2158, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1885, c_1889, c_2009, c_1882, c_2153])).
% 4.54/1.79  tff(c_1887, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1863, c_62])).
% 4.54/1.79  tff(c_2124, plain, (![A_268, B_269]: (k2_funct_2(A_268, B_269)=k2_funct_1(B_269) | ~m1_subset_1(B_269, k1_zfmisc_1(k2_zfmisc_1(A_268, A_268))) | ~v3_funct_2(B_269, A_268, A_268) | ~v1_funct_2(B_269, A_268, A_268) | ~v1_funct_1(B_269))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.54/1.79  tff(c_2127, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_1886, c_2124])).
% 4.54/1.79  tff(c_2133, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1889, c_1887, c_1888, c_2127])).
% 4.54/1.79  tff(c_1580, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1574, c_54])).
% 4.54/1.79  tff(c_1881, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1863, c_1863, c_1580])).
% 4.54/1.79  tff(c_2135, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2133, c_1881])).
% 4.54/1.79  tff(c_2160, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2158, c_2135])).
% 4.54/1.79  tff(c_2164, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1866, c_2160])).
% 4.54/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.54/1.79  
% 4.54/1.79  Inference rules
% 4.54/1.79  ----------------------
% 4.54/1.79  #Ref     : 0
% 4.54/1.79  #Sup     : 463
% 4.54/1.79  #Fact    : 0
% 4.54/1.79  #Define  : 0
% 4.54/1.79  #Split   : 18
% 4.54/1.79  #Chain   : 0
% 4.54/1.79  #Close   : 0
% 4.54/1.79  
% 4.54/1.79  Ordering : KBO
% 4.54/1.79  
% 4.54/1.79  Simplification rules
% 4.54/1.79  ----------------------
% 4.54/1.79  #Subsume      : 35
% 4.54/1.79  #Demod        : 515
% 4.54/1.79  #Tautology    : 254
% 4.54/1.79  #SimpNegUnit  : 15
% 4.54/1.79  #BackRed      : 76
% 4.54/1.79  
% 4.54/1.79  #Partial instantiations: 0
% 4.54/1.79  #Strategies tried      : 1
% 4.54/1.79  
% 4.54/1.79  Timing (in seconds)
% 4.54/1.79  ----------------------
% 4.54/1.79  Preprocessing        : 0.35
% 4.54/1.79  Parsing              : 0.19
% 4.54/1.79  CNF conversion       : 0.02
% 4.54/1.79  Main loop            : 0.63
% 4.54/1.79  Inferencing          : 0.24
% 4.54/1.79  Reduction            : 0.21
% 4.54/1.79  Demodulation         : 0.15
% 4.54/1.79  BG Simplification    : 0.03
% 4.54/1.79  Subsumption          : 0.10
% 4.54/1.79  Abstraction          : 0.03
% 4.54/1.79  MUC search           : 0.00
% 4.54/1.79  Cooper               : 0.00
% 4.54/1.79  Total                : 1.04
% 4.54/1.79  Index Insertion      : 0.00
% 4.54/1.79  Index Deletion       : 0.00
% 4.54/1.79  Index Matching       : 0.00
% 4.54/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
