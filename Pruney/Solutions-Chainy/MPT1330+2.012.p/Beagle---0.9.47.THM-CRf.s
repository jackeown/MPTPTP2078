%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:10 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 832 expanded)
%              Number of leaves         :   47 ( 301 expanded)
%              Depth                    :   16
%              Number of atoms          :  221 (2102 expanded)
%              Number of equality atoms :   79 ( 813 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_150,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( l1_struct_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_struct_0(B) = k1_xboole_0
                   => k2_struct_0(A) = k1_xboole_0 )
                 => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,k2_struct_0(B)) = k2_struct_0(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tops_2)).

tff(f_131,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_56,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_127,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_102,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_63,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(c_6,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_64,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_132,plain,(
    ! [A_64] :
      ( u1_struct_0(A_64) = k2_struct_0(A_64)
      | ~ l1_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_140,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_132])).

tff(c_62,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_139,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_132])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_141,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_56])).

tff(c_169,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_141])).

tff(c_30,plain,(
    ! [C_17,A_15,B_16] :
      ( v1_relat_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_173,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_169,c_30])).

tff(c_179,plain,(
    ! [C_74,B_75,A_76] :
      ( v5_relat_1(C_74,B_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_76,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_189,plain,(
    v5_relat_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_169,c_179])).

tff(c_14,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_259,plain,(
    ! [B_93,A_94] :
      ( k5_relat_1(B_93,k6_relat_1(A_94)) = B_93
      | ~ r1_tarski(k2_relat_1(B_93),A_94)
      | ~ v1_relat_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_269,plain,(
    ! [B_7,A_6] :
      ( k5_relat_1(B_7,k6_relat_1(A_6)) = B_7
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_14,c_259])).

tff(c_26,plain,(
    ! [A_14] : v1_relat_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    ! [A_11] : k1_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_615,plain,(
    ! [A_136,B_137] :
      ( k10_relat_1(A_136,k1_relat_1(B_137)) = k1_relat_1(k5_relat_1(A_136,B_137))
      | ~ v1_relat_1(B_137)
      | ~ v1_relat_1(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_627,plain,(
    ! [A_136,A_11] :
      ( k1_relat_1(k5_relat_1(A_136,k6_relat_1(A_11))) = k10_relat_1(A_136,A_11)
      | ~ v1_relat_1(k6_relat_1(A_11))
      | ~ v1_relat_1(A_136) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_615])).

tff(c_679,plain,(
    ! [A_141,A_142] :
      ( k1_relat_1(k5_relat_1(A_141,k6_relat_1(A_142))) = k10_relat_1(A_141,A_142)
      | ~ v1_relat_1(A_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_627])).

tff(c_764,plain,(
    ! [B_148,A_149] :
      ( k10_relat_1(B_148,A_149) = k1_relat_1(B_148)
      | ~ v1_relat_1(B_148)
      | ~ v5_relat_1(B_148,A_149)
      | ~ v1_relat_1(B_148) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_679])).

tff(c_773,plain,
    ( k10_relat_1('#skF_4',k2_struct_0('#skF_3')) = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_189,c_764])).

tff(c_782,plain,(
    k10_relat_1('#skF_4',k2_struct_0('#skF_3')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_773])).

tff(c_236,plain,(
    ! [C_89,A_90,B_91] :
      ( v4_relat_1(C_89,A_90)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_246,plain,(
    v4_relat_1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_169,c_236])).

tff(c_294,plain,(
    ! [B_100,A_101] :
      ( k1_relat_1(B_100) = A_101
      | ~ v1_partfun1(B_100,A_101)
      | ~ v4_relat_1(B_100,A_101)
      | ~ v1_relat_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_297,plain,
    ( k2_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',k2_struct_0('#skF_2'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_246,c_294])).

tff(c_300,plain,
    ( k2_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_297])).

tff(c_301,plain,(
    ~ v1_partfun1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_300])).

tff(c_54,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | k2_struct_0('#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_76,plain,(
    k2_struct_0('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_58,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_142,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_58])).

tff(c_151,plain,(
    v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_142])).

tff(c_512,plain,(
    ! [B_130,C_131,A_132] :
      ( k1_xboole_0 = B_130
      | v1_partfun1(C_131,A_132)
      | ~ v1_funct_2(C_131,A_132,B_130)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_132,B_130)))
      | ~ v1_funct_1(C_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_515,plain,
    ( k2_struct_0('#skF_3') = k1_xboole_0
    | v1_partfun1('#skF_4',k2_struct_0('#skF_2'))
    | ~ v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k2_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_169,c_512])).

tff(c_524,plain,
    ( k2_struct_0('#skF_3') = k1_xboole_0
    | v1_partfun1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_151,c_515])).

tff(c_526,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_301,c_76,c_524])).

tff(c_527,plain,(
    k2_struct_0('#skF_2') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_300])).

tff(c_532,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_527,c_169])).

tff(c_866,plain,(
    ! [A_155,B_156,C_157,D_158] :
      ( k8_relset_1(A_155,B_156,C_157,D_158) = k10_relat_1(C_157,D_158)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_873,plain,(
    ! [D_158] : k8_relset_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),'#skF_4',D_158) = k10_relat_1('#skF_4',D_158) ),
    inference(resolution,[status(thm)],[c_532,c_866])).

tff(c_52,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k2_struct_0('#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_174,plain,(
    k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4',k2_struct_0('#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_139,c_52])).

tff(c_531,plain,(
    k8_relset_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),'#skF_4',k2_struct_0('#skF_3')) != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_527,c_527,c_174])).

tff(c_916,plain,(
    k10_relat_1('#skF_4',k2_struct_0('#skF_3')) != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_873,c_531])).

tff(c_919,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_782,c_916])).

tff(c_921,plain,(
    k2_struct_0('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_985,plain,(
    ! [A_165] :
      ( u1_struct_0(A_165) = k2_struct_0(A_165)
      | ~ l1_struct_0(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_988,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_985])).

tff(c_993,plain,(
    u1_struct_0('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_921,c_988])).

tff(c_1017,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_993,c_56])).

tff(c_8,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1018,plain,(
    ! [C_168,A_169,B_170] :
      ( v1_relat_1(C_168)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1024,plain,(
    ! [C_171] :
      ( v1_relat_1(C_171)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1018])).

tff(c_1028,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1017,c_1024])).

tff(c_40,plain,(
    ! [A_25] :
      ( r2_hidden('#skF_1'(A_25),A_25)
      | k1_xboole_0 = A_25 ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1029,plain,(
    ! [C_172,B_173,A_174] :
      ( ~ v1_xboole_0(C_172)
      | ~ m1_subset_1(B_173,k1_zfmisc_1(C_172))
      | ~ r2_hidden(A_174,B_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1031,plain,(
    ! [A_174] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_174,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1017,c_1029])).

tff(c_1035,plain,(
    ! [A_175] : ~ r2_hidden(A_175,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1031])).

tff(c_1040,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_1035])).

tff(c_24,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_952,plain,(
    ! [A_162] : k1_relat_1(k6_relat_1(A_162)) = A_162 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_961,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_952])).

tff(c_1061,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1040,c_1040,c_961])).

tff(c_1054,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1040,c_1017])).

tff(c_1062,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_4',B_2) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1040,c_1040,c_8])).

tff(c_1184,plain,(
    ! [C_185,B_186,A_187] :
      ( v5_relat_1(C_185,B_186)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_187,B_186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1215,plain,(
    ! [C_196,B_197] :
      ( v5_relat_1(C_196,B_197)
      | ~ m1_subset_1(C_196,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1062,c_1184])).

tff(c_1218,plain,(
    ! [B_197] : v5_relat_1('#skF_4',B_197) ),
    inference(resolution,[status(thm)],[c_1054,c_1215])).

tff(c_70,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_26])).

tff(c_968,plain,(
    ! [A_163] : k2_relat_1(k6_relat_1(A_163)) = A_163 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_977,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_968])).

tff(c_1041,plain,(
    ! [B_176,A_177] :
      ( r1_tarski(k2_relat_1(B_176),A_177)
      | ~ v5_relat_1(B_176,A_177)
      | ~ v1_relat_1(B_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1044,plain,(
    ! [A_177] :
      ( r1_tarski(k1_xboole_0,A_177)
      | ~ v5_relat_1(k1_xboole_0,A_177)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_977,c_1041])).

tff(c_1049,plain,(
    ! [A_177] :
      ( r1_tarski(k1_xboole_0,A_177)
      | ~ v5_relat_1(k1_xboole_0,A_177) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1044])).

tff(c_1169,plain,(
    ! [A_177] :
      ( r1_tarski('#skF_4',A_177)
      | ~ v5_relat_1('#skF_4',A_177) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1040,c_1040,c_1049])).

tff(c_1232,plain,(
    ! [A_177] : r1_tarski('#skF_4',A_177) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1218,c_1169])).

tff(c_1060,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1040,c_1040,c_977])).

tff(c_1274,plain,(
    ! [B_208,A_209] :
      ( k5_relat_1(B_208,k6_relat_1(A_209)) = B_208
      | ~ r1_tarski(k2_relat_1(B_208),A_209)
      | ~ v1_relat_1(B_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1277,plain,(
    ! [A_209] :
      ( k5_relat_1('#skF_4',k6_relat_1(A_209)) = '#skF_4'
      | ~ r1_tarski('#skF_4',A_209)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1060,c_1274])).

tff(c_1285,plain,(
    ! [A_209] : k5_relat_1('#skF_4',k6_relat_1(A_209)) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1028,c_1232,c_1277])).

tff(c_1334,plain,(
    ! [A_218,B_219] :
      ( k10_relat_1(A_218,k1_relat_1(B_219)) = k1_relat_1(k5_relat_1(A_218,B_219))
      | ~ v1_relat_1(B_219)
      | ~ v1_relat_1(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1346,plain,(
    ! [A_218,A_11] :
      ( k1_relat_1(k5_relat_1(A_218,k6_relat_1(A_11))) = k10_relat_1(A_218,A_11)
      | ~ v1_relat_1(k6_relat_1(A_11))
      | ~ v1_relat_1(A_218) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1334])).

tff(c_1388,plain,(
    ! [A_223,A_224] :
      ( k1_relat_1(k5_relat_1(A_223,k6_relat_1(A_224))) = k10_relat_1(A_223,A_224)
      | ~ v1_relat_1(A_223) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1346])).

tff(c_1403,plain,(
    ! [A_209] :
      ( k10_relat_1('#skF_4',A_209) = k1_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1285,c_1388])).

tff(c_1410,plain,(
    ! [A_209] : k10_relat_1('#skF_4',A_209) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1028,c_1061,c_1403])).

tff(c_1063,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1040,c_1040,c_6])).

tff(c_1509,plain,(
    ! [A_231,B_232,C_233,D_234] :
      ( k8_relset_1(A_231,B_232,C_233,D_234) = k10_relat_1(C_233,D_234)
      | ~ m1_subset_1(C_233,k1_zfmisc_1(k2_zfmisc_1(A_231,B_232))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1703,plain,(
    ! [A_248,C_249,D_250] :
      ( k8_relset_1(A_248,'#skF_4',C_249,D_250) = k10_relat_1(C_249,D_250)
      | ~ m1_subset_1(C_249,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1063,c_1509])).

tff(c_1705,plain,(
    ! [A_248,D_250] : k8_relset_1(A_248,'#skF_4','#skF_4',D_250) = k10_relat_1('#skF_4',D_250) ),
    inference(resolution,[status(thm)],[c_1054,c_1703])).

tff(c_1707,plain,(
    ! [A_248,D_250] : k8_relset_1(A_248,'#skF_4','#skF_4',D_250) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1410,c_1705])).

tff(c_920,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_991,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_985])).

tff(c_995,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_920,c_991])).

tff(c_1023,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_995,c_993,c_921,c_920,c_52])).

tff(c_1053,plain,(
    k8_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1040,c_1040,c_1040,c_1040,c_1023])).

tff(c_1710,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1707,c_1053])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:18:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.77/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.77/1.66  
% 3.77/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.77/1.66  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.77/1.66  
% 3.77/1.66  %Foreground sorts:
% 3.77/1.66  
% 3.77/1.66  
% 3.77/1.66  %Background operators:
% 3.77/1.66  
% 3.77/1.66  
% 3.77/1.66  %Foreground operators:
% 3.77/1.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.77/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.77/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.77/1.66  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.77/1.66  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.77/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.77/1.66  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.77/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.77/1.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.77/1.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.77/1.66  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.77/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.77/1.66  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.77/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.77/1.66  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.77/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.77/1.66  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.77/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.77/1.66  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.77/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.77/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.77/1.66  tff('#skF_4', type, '#skF_4': $i).
% 3.77/1.66  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.77/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.77/1.66  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.77/1.66  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.77/1.66  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.77/1.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.77/1.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.77/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.77/1.66  
% 3.95/1.68  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.95/1.68  tff(f_150, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_struct_0(B) = k1_xboole_0) => (k2_struct_0(A) = k1_xboole_0)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k2_struct_0(B)) = k2_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_tops_2)).
% 3.95/1.68  tff(f_131, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.95/1.68  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.95/1.68  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.95/1.68  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.95/1.68  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 3.95/1.68  tff(f_67, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.95/1.68  tff(f_56, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.95/1.68  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 3.95/1.68  tff(f_110, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 3.95/1.68  tff(f_127, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 3.95/1.68  tff(f_81, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.95/1.68  tff(f_102, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 3.95/1.68  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.95/1.68  tff(f_39, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.95/1.68  tff(f_63, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 3.95/1.68  tff(c_6, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.95/1.68  tff(c_64, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.95/1.68  tff(c_132, plain, (![A_64]: (u1_struct_0(A_64)=k2_struct_0(A_64) | ~l1_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.95/1.68  tff(c_140, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_132])).
% 3.95/1.68  tff(c_62, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.95/1.68  tff(c_139, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_132])).
% 3.95/1.68  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.95/1.68  tff(c_141, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_56])).
% 3.95/1.68  tff(c_169, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_141])).
% 3.95/1.68  tff(c_30, plain, (![C_17, A_15, B_16]: (v1_relat_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.95/1.68  tff(c_173, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_169, c_30])).
% 3.95/1.68  tff(c_179, plain, (![C_74, B_75, A_76]: (v5_relat_1(C_74, B_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_76, B_75))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.95/1.68  tff(c_189, plain, (v5_relat_1('#skF_4', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_169, c_179])).
% 3.95/1.68  tff(c_14, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.95/1.68  tff(c_259, plain, (![B_93, A_94]: (k5_relat_1(B_93, k6_relat_1(A_94))=B_93 | ~r1_tarski(k2_relat_1(B_93), A_94) | ~v1_relat_1(B_93))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.95/1.68  tff(c_269, plain, (![B_7, A_6]: (k5_relat_1(B_7, k6_relat_1(A_6))=B_7 | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_14, c_259])).
% 3.95/1.68  tff(c_26, plain, (![A_14]: (v1_relat_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.95/1.68  tff(c_18, plain, (![A_11]: (k1_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.95/1.68  tff(c_615, plain, (![A_136, B_137]: (k10_relat_1(A_136, k1_relat_1(B_137))=k1_relat_1(k5_relat_1(A_136, B_137)) | ~v1_relat_1(B_137) | ~v1_relat_1(A_136))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.95/1.68  tff(c_627, plain, (![A_136, A_11]: (k1_relat_1(k5_relat_1(A_136, k6_relat_1(A_11)))=k10_relat_1(A_136, A_11) | ~v1_relat_1(k6_relat_1(A_11)) | ~v1_relat_1(A_136))), inference(superposition, [status(thm), theory('equality')], [c_18, c_615])).
% 3.95/1.68  tff(c_679, plain, (![A_141, A_142]: (k1_relat_1(k5_relat_1(A_141, k6_relat_1(A_142)))=k10_relat_1(A_141, A_142) | ~v1_relat_1(A_141))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_627])).
% 3.95/1.68  tff(c_764, plain, (![B_148, A_149]: (k10_relat_1(B_148, A_149)=k1_relat_1(B_148) | ~v1_relat_1(B_148) | ~v5_relat_1(B_148, A_149) | ~v1_relat_1(B_148))), inference(superposition, [status(thm), theory('equality')], [c_269, c_679])).
% 3.95/1.68  tff(c_773, plain, (k10_relat_1('#skF_4', k2_struct_0('#skF_3'))=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_189, c_764])).
% 3.95/1.68  tff(c_782, plain, (k10_relat_1('#skF_4', k2_struct_0('#skF_3'))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_773])).
% 3.95/1.68  tff(c_236, plain, (![C_89, A_90, B_91]: (v4_relat_1(C_89, A_90) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.95/1.68  tff(c_246, plain, (v4_relat_1('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_169, c_236])).
% 3.95/1.68  tff(c_294, plain, (![B_100, A_101]: (k1_relat_1(B_100)=A_101 | ~v1_partfun1(B_100, A_101) | ~v4_relat_1(B_100, A_101) | ~v1_relat_1(B_100))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.95/1.68  tff(c_297, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', k2_struct_0('#skF_2')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_246, c_294])).
% 3.95/1.68  tff(c_300, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_297])).
% 3.95/1.68  tff(c_301, plain, (~v1_partfun1('#skF_4', k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_300])).
% 3.95/1.68  tff(c_54, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | k2_struct_0('#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.95/1.68  tff(c_76, plain, (k2_struct_0('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_54])).
% 3.95/1.68  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.95/1.68  tff(c_58, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.95/1.68  tff(c_142, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_58])).
% 3.95/1.68  tff(c_151, plain, (v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_142])).
% 3.95/1.68  tff(c_512, plain, (![B_130, C_131, A_132]: (k1_xboole_0=B_130 | v1_partfun1(C_131, A_132) | ~v1_funct_2(C_131, A_132, B_130) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_132, B_130))) | ~v1_funct_1(C_131))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.95/1.68  tff(c_515, plain, (k2_struct_0('#skF_3')=k1_xboole_0 | v1_partfun1('#skF_4', k2_struct_0('#skF_2')) | ~v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k2_struct_0('#skF_3')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_169, c_512])).
% 3.95/1.68  tff(c_524, plain, (k2_struct_0('#skF_3')=k1_xboole_0 | v1_partfun1('#skF_4', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_151, c_515])).
% 3.95/1.68  tff(c_526, plain, $false, inference(negUnitSimplification, [status(thm)], [c_301, c_76, c_524])).
% 3.95/1.68  tff(c_527, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_300])).
% 3.95/1.68  tff(c_532, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_527, c_169])).
% 3.95/1.68  tff(c_866, plain, (![A_155, B_156, C_157, D_158]: (k8_relset_1(A_155, B_156, C_157, D_158)=k10_relat_1(C_157, D_158) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.95/1.68  tff(c_873, plain, (![D_158]: (k8_relset_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), '#skF_4', D_158)=k10_relat_1('#skF_4', D_158))), inference(resolution, [status(thm)], [c_532, c_866])).
% 3.95/1.68  tff(c_52, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k2_struct_0('#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.95/1.68  tff(c_174, plain, (k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4', k2_struct_0('#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_139, c_52])).
% 3.95/1.68  tff(c_531, plain, (k8_relset_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), '#skF_4', k2_struct_0('#skF_3'))!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_527, c_527, c_174])).
% 3.95/1.68  tff(c_916, plain, (k10_relat_1('#skF_4', k2_struct_0('#skF_3'))!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_873, c_531])).
% 3.95/1.68  tff(c_919, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_782, c_916])).
% 3.95/1.68  tff(c_921, plain, (k2_struct_0('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 3.95/1.68  tff(c_985, plain, (![A_165]: (u1_struct_0(A_165)=k2_struct_0(A_165) | ~l1_struct_0(A_165))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.95/1.68  tff(c_988, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_985])).
% 3.95/1.68  tff(c_993, plain, (u1_struct_0('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_921, c_988])).
% 3.95/1.68  tff(c_1017, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_993, c_56])).
% 3.95/1.68  tff(c_8, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.95/1.68  tff(c_1018, plain, (![C_168, A_169, B_170]: (v1_relat_1(C_168) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.95/1.68  tff(c_1024, plain, (![C_171]: (v1_relat_1(C_171) | ~m1_subset_1(C_171, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1018])).
% 3.95/1.68  tff(c_1028, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1017, c_1024])).
% 3.95/1.68  tff(c_40, plain, (![A_25]: (r2_hidden('#skF_1'(A_25), A_25) | k1_xboole_0=A_25)), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.95/1.68  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.95/1.68  tff(c_1029, plain, (![C_172, B_173, A_174]: (~v1_xboole_0(C_172) | ~m1_subset_1(B_173, k1_zfmisc_1(C_172)) | ~r2_hidden(A_174, B_173))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.95/1.68  tff(c_1031, plain, (![A_174]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_174, '#skF_4'))), inference(resolution, [status(thm)], [c_1017, c_1029])).
% 3.95/1.68  tff(c_1035, plain, (![A_175]: (~r2_hidden(A_175, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1031])).
% 3.95/1.68  tff(c_1040, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_40, c_1035])).
% 3.95/1.68  tff(c_24, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.95/1.68  tff(c_952, plain, (![A_162]: (k1_relat_1(k6_relat_1(A_162))=A_162)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.95/1.68  tff(c_961, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_24, c_952])).
% 3.95/1.68  tff(c_1061, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1040, c_1040, c_961])).
% 3.95/1.68  tff(c_1054, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1040, c_1017])).
% 3.95/1.68  tff(c_1062, plain, (![B_2]: (k2_zfmisc_1('#skF_4', B_2)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1040, c_1040, c_8])).
% 3.95/1.68  tff(c_1184, plain, (![C_185, B_186, A_187]: (v5_relat_1(C_185, B_186) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_187, B_186))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.95/1.68  tff(c_1215, plain, (![C_196, B_197]: (v5_relat_1(C_196, B_197) | ~m1_subset_1(C_196, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1062, c_1184])).
% 3.95/1.68  tff(c_1218, plain, (![B_197]: (v5_relat_1('#skF_4', B_197))), inference(resolution, [status(thm)], [c_1054, c_1215])).
% 3.95/1.68  tff(c_70, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_26])).
% 3.95/1.68  tff(c_968, plain, (![A_163]: (k2_relat_1(k6_relat_1(A_163))=A_163)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.95/1.68  tff(c_977, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_24, c_968])).
% 3.95/1.68  tff(c_1041, plain, (![B_176, A_177]: (r1_tarski(k2_relat_1(B_176), A_177) | ~v5_relat_1(B_176, A_177) | ~v1_relat_1(B_176))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.95/1.68  tff(c_1044, plain, (![A_177]: (r1_tarski(k1_xboole_0, A_177) | ~v5_relat_1(k1_xboole_0, A_177) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_977, c_1041])).
% 3.95/1.68  tff(c_1049, plain, (![A_177]: (r1_tarski(k1_xboole_0, A_177) | ~v5_relat_1(k1_xboole_0, A_177))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1044])).
% 3.95/1.68  tff(c_1169, plain, (![A_177]: (r1_tarski('#skF_4', A_177) | ~v5_relat_1('#skF_4', A_177))), inference(demodulation, [status(thm), theory('equality')], [c_1040, c_1040, c_1049])).
% 3.95/1.68  tff(c_1232, plain, (![A_177]: (r1_tarski('#skF_4', A_177))), inference(demodulation, [status(thm), theory('equality')], [c_1218, c_1169])).
% 3.95/1.68  tff(c_1060, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1040, c_1040, c_977])).
% 3.95/1.68  tff(c_1274, plain, (![B_208, A_209]: (k5_relat_1(B_208, k6_relat_1(A_209))=B_208 | ~r1_tarski(k2_relat_1(B_208), A_209) | ~v1_relat_1(B_208))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.95/1.68  tff(c_1277, plain, (![A_209]: (k5_relat_1('#skF_4', k6_relat_1(A_209))='#skF_4' | ~r1_tarski('#skF_4', A_209) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1060, c_1274])).
% 3.95/1.68  tff(c_1285, plain, (![A_209]: (k5_relat_1('#skF_4', k6_relat_1(A_209))='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1028, c_1232, c_1277])).
% 3.95/1.68  tff(c_1334, plain, (![A_218, B_219]: (k10_relat_1(A_218, k1_relat_1(B_219))=k1_relat_1(k5_relat_1(A_218, B_219)) | ~v1_relat_1(B_219) | ~v1_relat_1(A_218))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.95/1.68  tff(c_1346, plain, (![A_218, A_11]: (k1_relat_1(k5_relat_1(A_218, k6_relat_1(A_11)))=k10_relat_1(A_218, A_11) | ~v1_relat_1(k6_relat_1(A_11)) | ~v1_relat_1(A_218))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1334])).
% 3.95/1.68  tff(c_1388, plain, (![A_223, A_224]: (k1_relat_1(k5_relat_1(A_223, k6_relat_1(A_224)))=k10_relat_1(A_223, A_224) | ~v1_relat_1(A_223))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1346])).
% 3.95/1.68  tff(c_1403, plain, (![A_209]: (k10_relat_1('#skF_4', A_209)=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1285, c_1388])).
% 3.95/1.68  tff(c_1410, plain, (![A_209]: (k10_relat_1('#skF_4', A_209)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1028, c_1061, c_1403])).
% 3.95/1.68  tff(c_1063, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1040, c_1040, c_6])).
% 3.95/1.68  tff(c_1509, plain, (![A_231, B_232, C_233, D_234]: (k8_relset_1(A_231, B_232, C_233, D_234)=k10_relat_1(C_233, D_234) | ~m1_subset_1(C_233, k1_zfmisc_1(k2_zfmisc_1(A_231, B_232))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.95/1.68  tff(c_1703, plain, (![A_248, C_249, D_250]: (k8_relset_1(A_248, '#skF_4', C_249, D_250)=k10_relat_1(C_249, D_250) | ~m1_subset_1(C_249, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1063, c_1509])).
% 3.95/1.68  tff(c_1705, plain, (![A_248, D_250]: (k8_relset_1(A_248, '#skF_4', '#skF_4', D_250)=k10_relat_1('#skF_4', D_250))), inference(resolution, [status(thm)], [c_1054, c_1703])).
% 3.95/1.68  tff(c_1707, plain, (![A_248, D_250]: (k8_relset_1(A_248, '#skF_4', '#skF_4', D_250)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1410, c_1705])).
% 3.95/1.68  tff(c_920, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 3.95/1.68  tff(c_991, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_985])).
% 3.95/1.68  tff(c_995, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_920, c_991])).
% 3.95/1.68  tff(c_1023, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_4', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_995, c_993, c_921, c_920, c_52])).
% 3.95/1.68  tff(c_1053, plain, (k8_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1040, c_1040, c_1040, c_1040, c_1023])).
% 3.95/1.68  tff(c_1710, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1707, c_1053])).
% 3.95/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.68  
% 3.95/1.68  Inference rules
% 3.95/1.68  ----------------------
% 3.95/1.68  #Ref     : 0
% 3.95/1.68  #Sup     : 373
% 3.95/1.68  #Fact    : 0
% 3.95/1.68  #Define  : 0
% 3.95/1.68  #Split   : 6
% 3.95/1.68  #Chain   : 0
% 3.95/1.68  #Close   : 0
% 3.95/1.68  
% 3.95/1.68  Ordering : KBO
% 3.95/1.68  
% 3.95/1.68  Simplification rules
% 3.95/1.68  ----------------------
% 3.95/1.68  #Subsume      : 56
% 3.95/1.68  #Demod        : 275
% 3.95/1.68  #Tautology    : 205
% 3.95/1.68  #SimpNegUnit  : 1
% 3.95/1.68  #BackRed      : 32
% 3.95/1.68  
% 3.95/1.68  #Partial instantiations: 0
% 3.95/1.68  #Strategies tried      : 1
% 3.95/1.68  
% 3.95/1.68  Timing (in seconds)
% 3.95/1.68  ----------------------
% 3.95/1.69  Preprocessing        : 0.36
% 3.95/1.69  Parsing              : 0.20
% 3.95/1.69  CNF conversion       : 0.02
% 3.95/1.69  Main loop            : 0.48
% 3.95/1.69  Inferencing          : 0.18
% 3.95/1.69  Reduction            : 0.16
% 3.95/1.69  Demodulation         : 0.11
% 3.95/1.69  BG Simplification    : 0.02
% 3.95/1.69  Subsumption          : 0.07
% 3.95/1.69  Abstraction          : 0.02
% 3.95/1.69  MUC search           : 0.00
% 3.95/1.69  Cooper               : 0.00
% 3.95/1.69  Total                : 0.89
% 3.95/1.69  Index Insertion      : 0.00
% 3.95/1.69  Index Deletion       : 0.00
% 3.95/1.69  Index Matching       : 0.00
% 3.95/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
