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
% DateTime   : Thu Dec  3 10:23:13 EST 2020

% Result     : Theorem 8.27s
% Output     : CNFRefutation 8.54s
% Verified   : 
% Statistics : Number of formulae       :  307 (10036 expanded)
%              Number of leaves         :   70 (3506 expanded)
%              Depth                    :   25
%              Number of atoms          :  524 (29793 expanded)
%              Number of equality atoms :  152 (9331 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k3_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k10_relat_1 > #nlpp > u1_struct_0 > k4_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_relset_1,type,(
    k3_relset_1: ( $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_239,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_struct_0(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                    & v2_funct_1(C) )
                 => ( k1_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(B)
                    & k2_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

tff(f_195,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_90,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_36,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_149,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_203,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_103,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_137,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_175,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_167,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_215,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_119,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_153,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k3_relset_1(A,B,C) = k4_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

tff(f_141,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k3_relset_1(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_relset_1)).

tff(f_131,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_191,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_145,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_52,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_101,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_107,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_127,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_111,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(c_112,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_110,plain,(
    l1_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_114,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_136,plain,(
    ! [A_89] :
      ( u1_struct_0(A_89) = k2_struct_0(A_89)
      | ~ l1_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_144,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_114,c_136])).

tff(c_143,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_110,c_136])).

tff(c_104,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_237,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_143,c_104])).

tff(c_272,plain,(
    ! [A_110,B_111] :
      ( r1_tarski(A_110,B_111)
      | ~ m1_subset_1(A_110,k1_zfmisc_1(B_111)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_280,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_237,c_272])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( k3_xboole_0(A_13,B_14) = A_13
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_5584,plain,(
    k3_xboole_0('#skF_6',k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'))) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_280,c_18])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_xboole_0(A_5,B_6)
      | k3_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5737,plain,(
    ! [B_502,A_503] :
      ( ~ r1_xboole_0(B_502,A_503)
      | ~ r1_tarski(B_502,A_503)
      | v1_xboole_0(B_502) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6201,plain,(
    ! [A_560,B_561] :
      ( ~ r1_tarski(A_560,B_561)
      | v1_xboole_0(A_560)
      | k3_xboole_0(A_560,B_561) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_5737])).

tff(c_6210,plain,
    ( v1_xboole_0('#skF_6')
    | k3_xboole_0('#skF_6',k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_280,c_6201])).

tff(c_6219,plain,
    ( v1_xboole_0('#skF_6')
    | k1_xboole_0 != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5584,c_6210])).

tff(c_6222,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_6219])).

tff(c_10,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_42,plain,(
    ! [A_28,B_29] :
      ( v1_xboole_0(k2_zfmisc_1(A_28,B_29))
      | ~ v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_165,plain,(
    ! [B_93,A_94] :
      ( ~ v1_xboole_0(B_93)
      | B_93 = A_94
      | ~ v1_xboole_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_175,plain,(
    ! [A_95] :
      ( k1_xboole_0 = A_95
      | ~ v1_xboole_0(A_95) ) ),
    inference(resolution,[status(thm)],[c_10,c_165])).

tff(c_213,plain,(
    ! [A_99,B_100] :
      ( k2_zfmisc_1(A_99,B_100) = k1_xboole_0
      | ~ v1_xboole_0(A_99) ) ),
    inference(resolution,[status(thm)],[c_42,c_175])).

tff(c_222,plain,(
    ! [B_100] : k2_zfmisc_1(k1_xboole_0,B_100) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_213])).

tff(c_108,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_6665,plain,(
    ! [A_606,B_607,C_608] :
      ( k2_relset_1(A_606,B_607,C_608) = k2_relat_1(C_608)
      | ~ m1_subset_1(C_608,k1_zfmisc_1(k2_zfmisc_1(A_606,B_607))) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_6686,plain,(
    k2_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'),'#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_237,c_6665])).

tff(c_102,plain,(
    k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') = k2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_160,plain,(
    k2_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'),'#skF_6') = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_143,c_102])).

tff(c_6695,plain,(
    k2_struct_0('#skF_5') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6686,c_160])).

tff(c_94,plain,(
    ! [A_72] :
      ( ~ v1_xboole_0(k2_struct_0(A_72))
      | ~ l1_struct_0(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_6714,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_6'))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6695,c_94])).

tff(c_6718,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_6714])).

tff(c_6719,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_6718])).

tff(c_54,plain,(
    ! [A_37,B_38] : v1_relat_1(k2_zfmisc_1(A_37,B_38)) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_5543,plain,(
    ! [B_482,A_483] :
      ( v1_relat_1(B_482)
      | ~ m1_subset_1(B_482,k1_zfmisc_1(A_483))
      | ~ v1_relat_1(A_483) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_5549,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_237,c_5543])).

tff(c_5553,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_5549])).

tff(c_6022,plain,(
    ! [C_542,A_543,B_544] :
      ( v4_relat_1(C_542,A_543)
      | ~ m1_subset_1(C_542,k1_zfmisc_1(k2_zfmisc_1(A_543,B_544))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_6040,plain,(
    v4_relat_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_237,c_6022])).

tff(c_6366,plain,(
    ! [B_576,A_577] :
      ( k1_relat_1(B_576) = A_577
      | ~ v1_partfun1(B_576,A_577)
      | ~ v4_relat_1(B_576,A_577)
      | ~ v1_relat_1(B_576) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_6378,plain,
    ( k2_struct_0('#skF_4') = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',k2_struct_0('#skF_4'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_6040,c_6366])).

tff(c_6388,plain,
    ( k2_struct_0('#skF_4') = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5553,c_6378])).

tff(c_6395,plain,(
    ~ v1_partfun1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_6388])).

tff(c_106,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_146,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_106])).

tff(c_211,plain,(
    v1_funct_2('#skF_6',k2_struct_0('#skF_4'),k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_146])).

tff(c_6709,plain,(
    v1_funct_2('#skF_6',k2_struct_0('#skF_4'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6695,c_211])).

tff(c_6708,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_relat_1('#skF_6')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6695,c_237])).

tff(c_7944,plain,(
    ! [C_686,A_687,B_688] :
      ( v1_partfun1(C_686,A_687)
      | ~ v1_funct_2(C_686,A_687,B_688)
      | ~ v1_funct_1(C_686)
      | ~ m1_subset_1(C_686,k1_zfmisc_1(k2_zfmisc_1(A_687,B_688)))
      | v1_xboole_0(B_688) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_7953,plain,
    ( v1_partfun1('#skF_6',k2_struct_0('#skF_4'))
    | ~ v1_funct_2('#skF_6',k2_struct_0('#skF_4'),k2_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_6708,c_7944])).

tff(c_7974,plain,
    ( v1_partfun1('#skF_6',k2_struct_0('#skF_4'))
    | v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_6709,c_7953])).

tff(c_7976,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6719,c_6395,c_7974])).

tff(c_7977,plain,(
    k2_struct_0('#skF_4') = k1_relat_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_6388])).

tff(c_7985,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),k2_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7977,c_237])).

tff(c_8336,plain,(
    ! [A_713,B_714,C_715] :
      ( k2_relset_1(A_713,B_714,C_715) = k2_relat_1(C_715)
      | ~ m1_subset_1(C_715,k1_zfmisc_1(k2_zfmisc_1(A_713,B_714))) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_8356,plain,(
    k2_relset_1(k1_relat_1('#skF_6'),k2_struct_0('#skF_5'),'#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_7985,c_8336])).

tff(c_7987,plain,(
    k2_relset_1(k1_relat_1('#skF_6'),k2_struct_0('#skF_5'),'#skF_6') = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7977,c_160])).

tff(c_8358,plain,(
    k2_struct_0('#skF_5') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8356,c_7987])).

tff(c_7986,plain,(
    v1_funct_2('#skF_6',k1_relat_1('#skF_6'),k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7977,c_211])).

tff(c_8372,plain,(
    v1_funct_2('#skF_6',k1_relat_1('#skF_6'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8358,c_7986])).

tff(c_8363,plain,(
    k2_relset_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8358,c_8356])).

tff(c_100,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_8370,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8358,c_7985])).

tff(c_9735,plain,(
    ! [A_783,B_784,C_785] :
      ( k2_tops_2(A_783,B_784,C_785) = k2_funct_1(C_785)
      | ~ v2_funct_1(C_785)
      | k2_relset_1(A_783,B_784,C_785) != B_784
      | ~ m1_subset_1(C_785,k1_zfmisc_1(k2_zfmisc_1(A_783,B_784)))
      | ~ v1_funct_2(C_785,A_783,B_784)
      | ~ v1_funct_1(C_785) ) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_9747,plain,
    ( k2_tops_2(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6') = k2_funct_1('#skF_6')
    | ~ v2_funct_1('#skF_6')
    | k2_relset_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6') != k2_relat_1('#skF_6')
    | ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),k2_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_8370,c_9735])).

tff(c_9771,plain,(
    k2_tops_2(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6') = k2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_8372,c_8363,c_100,c_9747])).

tff(c_390,plain,(
    k3_xboole_0('#skF_6',k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'))) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_280,c_18])).

tff(c_470,plain,(
    ! [B_131,A_132] :
      ( ~ r1_xboole_0(B_131,A_132)
      | ~ r1_tarski(B_131,A_132)
      | v1_xboole_0(B_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_949,plain,(
    ! [A_190,B_191] :
      ( ~ r1_tarski(A_190,B_191)
      | v1_xboole_0(A_190)
      | k3_xboole_0(A_190,B_191) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_470])).

tff(c_958,plain,
    ( v1_xboole_0('#skF_6')
    | k3_xboole_0('#skF_6',k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_280,c_949])).

tff(c_967,plain,
    ( v1_xboole_0('#skF_6')
    | k1_xboole_0 != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_958])).

tff(c_970,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_967])).

tff(c_1703,plain,(
    ! [A_257,B_258,C_259] :
      ( k2_relset_1(A_257,B_258,C_259) = k2_relat_1(C_259)
      | ~ m1_subset_1(C_259,k1_zfmisc_1(k2_zfmisc_1(A_257,B_258))) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1724,plain,(
    k2_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'),'#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_237,c_1703])).

tff(c_1725,plain,(
    k2_struct_0('#skF_5') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1724,c_160])).

tff(c_1744,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_6'))
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1725,c_94])).

tff(c_1748,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_1744])).

tff(c_1749,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_1748])).

tff(c_353,plain,(
    ! [B_119,A_120] :
      ( v1_relat_1(B_119)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(A_120))
      | ~ v1_relat_1(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_359,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_237,c_353])).

tff(c_363,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_359])).

tff(c_786,plain,(
    ! [C_174,A_175,B_176] :
      ( v4_relat_1(C_174,A_175)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_175,B_176))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_801,plain,(
    v4_relat_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_237,c_786])).

tff(c_1191,plain,(
    ! [B_215,A_216] :
      ( k1_relat_1(B_215) = A_216
      | ~ v1_partfun1(B_215,A_216)
      | ~ v4_relat_1(B_215,A_216)
      | ~ v1_relat_1(B_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_1206,plain,
    ( k2_struct_0('#skF_4') = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',k2_struct_0('#skF_4'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_801,c_1191])).

tff(c_1217,plain,
    ( k2_struct_0('#skF_4') = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_1206])).

tff(c_1224,plain,(
    ~ v1_partfun1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1217])).

tff(c_1739,plain,(
    v1_funct_2('#skF_6',k2_struct_0('#skF_4'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1725,c_211])).

tff(c_1738,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_relat_1('#skF_6')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1725,c_237])).

tff(c_2751,plain,(
    ! [C_323,A_324,B_325] :
      ( v1_partfun1(C_323,A_324)
      | ~ v1_funct_2(C_323,A_324,B_325)
      | ~ v1_funct_1(C_323)
      | ~ m1_subset_1(C_323,k1_zfmisc_1(k2_zfmisc_1(A_324,B_325)))
      | v1_xboole_0(B_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_2760,plain,
    ( v1_partfun1('#skF_6',k2_struct_0('#skF_4'))
    | ~ v1_funct_2('#skF_6',k2_struct_0('#skF_4'),k2_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_1738,c_2751])).

tff(c_2781,plain,
    ( v1_partfun1('#skF_6',k2_struct_0('#skF_4'))
    | v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_1739,c_2760])).

tff(c_2783,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1749,c_1224,c_2781])).

tff(c_2784,plain,(
    k2_struct_0('#skF_4') = k1_relat_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_1217])).

tff(c_2791,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),k2_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2784,c_237])).

tff(c_3124,plain,(
    ! [A_350,B_351,C_352] :
      ( k2_relset_1(A_350,B_351,C_352) = k2_relat_1(C_352)
      | ~ m1_subset_1(C_352,k1_zfmisc_1(k2_zfmisc_1(A_350,B_351))) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_3144,plain,(
    k2_relset_1(k1_relat_1('#skF_6'),k2_struct_0('#skF_5'),'#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2791,c_3124])).

tff(c_2793,plain,(
    k2_relset_1(k1_relat_1('#skF_6'),k2_struct_0('#skF_5'),'#skF_6') = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2784,c_160])).

tff(c_3146,plain,(
    k2_struct_0('#skF_5') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3144,c_2793])).

tff(c_2792,plain,(
    v1_funct_2('#skF_6',k1_relat_1('#skF_6'),k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2784,c_211])).

tff(c_3159,plain,(
    v1_funct_2('#skF_6',k1_relat_1('#skF_6'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3146,c_2792])).

tff(c_3151,plain,(
    k2_relset_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3146,c_3144])).

tff(c_3157,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3146,c_2791])).

tff(c_4937,plain,(
    ! [A_450,B_451,C_452] :
      ( k2_tops_2(A_450,B_451,C_452) = k2_funct_1(C_452)
      | ~ v2_funct_1(C_452)
      | k2_relset_1(A_450,B_451,C_452) != B_451
      | ~ m1_subset_1(C_452,k1_zfmisc_1(k2_zfmisc_1(A_450,B_451)))
      | ~ v1_funct_2(C_452,A_450,B_451)
      | ~ v1_funct_1(C_452) ) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_4946,plain,
    ( k2_tops_2(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6') = k2_funct_1('#skF_6')
    | ~ v2_funct_1('#skF_6')
    | k2_relset_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6') != k2_relat_1('#skF_6')
    | ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),k2_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_3157,c_4937])).

tff(c_4969,plain,(
    k2_tops_2(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6') = k2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_3159,c_3151,c_100,c_4946])).

tff(c_98,plain,
    ( k2_relset_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')) != k2_struct_0('#skF_4')
    | k1_relset_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')) != k2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_314,plain,
    ( k2_relset_1(k2_struct_0('#skF_5'),k2_struct_0('#skF_4'),k2_tops_2(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'),'#skF_6')) != k2_struct_0('#skF_4')
    | k1_relset_1(k2_struct_0('#skF_5'),k2_struct_0('#skF_4'),k2_tops_2(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'),'#skF_6')) != k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_144,c_143,c_143,c_144,c_144,c_143,c_143,c_98])).

tff(c_315,plain,(
    k1_relset_1(k2_struct_0('#skF_5'),k2_struct_0('#skF_4'),k2_tops_2(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'),'#skF_6')) != k2_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_314])).

tff(c_2789,plain,(
    k1_relset_1(k2_struct_0('#skF_5'),k1_relat_1('#skF_6'),k2_tops_2(k1_relat_1('#skF_6'),k2_struct_0('#skF_5'),'#skF_6')) != k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2784,c_2784,c_315])).

tff(c_3155,plain,(
    k1_relset_1(k2_relat_1('#skF_6'),k1_relat_1('#skF_6'),k2_tops_2(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6')) != k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3146,c_3146,c_3146,c_2789])).

tff(c_4971,plain,(
    k1_relset_1(k2_relat_1('#skF_6'),k1_relat_1('#skF_6'),k2_funct_1('#skF_6')) != k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4969,c_3155])).

tff(c_912,plain,(
    ! [A_188] :
      ( k4_relat_1(A_188) = k2_funct_1(A_188)
      | ~ v2_funct_1(A_188)
      | ~ v1_funct_1(A_188)
      | ~ v1_relat_1(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_915,plain,
    ( k4_relat_1('#skF_6') = k2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_100,c_912])).

tff(c_918,plain,(
    k4_relat_1('#skF_6') = k2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_108,c_915])).

tff(c_2878,plain,(
    ! [A_326,B_327,C_328] :
      ( k3_relset_1(A_326,B_327,C_328) = k4_relat_1(C_328)
      | ~ m1_subset_1(C_328,k1_zfmisc_1(k2_zfmisc_1(A_326,B_327))) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_2881,plain,(
    k3_relset_1(k1_relat_1('#skF_6'),k2_struct_0('#skF_5'),'#skF_6') = k4_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2791,c_2878])).

tff(c_2896,plain,(
    k3_relset_1(k1_relat_1('#skF_6'),k2_struct_0('#skF_5'),'#skF_6') = k2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_918,c_2881])).

tff(c_3154,plain,(
    k3_relset_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6') = k2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3146,c_2896])).

tff(c_3971,plain,(
    ! [A_406,B_407,C_408] :
      ( m1_subset_1(k3_relset_1(A_406,B_407,C_408),k1_zfmisc_1(k2_zfmisc_1(B_407,A_406)))
      | ~ m1_subset_1(C_408,k1_zfmisc_1(k2_zfmisc_1(A_406,B_407))) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_4001,plain,
    ( m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_6'),k1_relat_1('#skF_6'))))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3154,c_3971])).

tff(c_4025,plain,(
    m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_6'),k1_relat_1('#skF_6')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3157,c_4001])).

tff(c_64,plain,(
    ! [C_46,A_44,B_45] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_4058,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_4025,c_64])).

tff(c_68,plain,(
    ! [C_49,A_47,B_48] :
      ( v4_relat_1(C_49,A_47)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_4056,plain,(
    v4_relat_1(k2_funct_1('#skF_6'),k2_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_4025,c_68])).

tff(c_84,plain,(
    ! [B_67,A_66] :
      ( k1_relat_1(B_67) = A_66
      | ~ v1_partfun1(B_67,A_66)
      | ~ v4_relat_1(B_67,A_66)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_4066,plain,
    ( k1_relat_1(k2_funct_1('#skF_6')) = k2_relat_1('#skF_6')
    | ~ v1_partfun1(k2_funct_1('#skF_6'),k2_relat_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_4056,c_84])).

tff(c_4069,plain,
    ( k1_relat_1(k2_funct_1('#skF_6')) = k2_relat_1('#skF_6')
    | ~ v1_partfun1(k2_funct_1('#skF_6'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4058,c_4066])).

tff(c_4415,plain,(
    ~ v1_partfun1(k2_funct_1('#skF_6'),k2_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_4069])).

tff(c_4354,plain,(
    ! [C_423,A_424,B_425] :
      ( v1_funct_1(k2_funct_1(C_423))
      | k2_relset_1(A_424,B_425,C_423) != B_425
      | ~ v2_funct_1(C_423)
      | ~ m1_subset_1(C_423,k1_zfmisc_1(k2_zfmisc_1(A_424,B_425)))
      | ~ v1_funct_2(C_423,A_424,B_425)
      | ~ v1_funct_1(C_423) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_4363,plain,
    ( v1_funct_1(k2_funct_1('#skF_6'))
    | k2_relset_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6') != k2_relat_1('#skF_6')
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),k2_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_3157,c_4354])).

tff(c_4385,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_3159,c_100,c_3151,c_4363])).

tff(c_4416,plain,(
    ! [C_426,B_427,A_428] :
      ( v1_funct_2(k2_funct_1(C_426),B_427,A_428)
      | k2_relset_1(A_428,B_427,C_426) != B_427
      | ~ v2_funct_1(C_426)
      | ~ m1_subset_1(C_426,k1_zfmisc_1(k2_zfmisc_1(A_428,B_427)))
      | ~ v1_funct_2(C_426,A_428,B_427)
      | ~ v1_funct_1(C_426) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_4425,plain,
    ( v1_funct_2(k2_funct_1('#skF_6'),k2_relat_1('#skF_6'),k1_relat_1('#skF_6'))
    | k2_relset_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6') != k2_relat_1('#skF_6')
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),k2_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_3157,c_4416])).

tff(c_4448,plain,(
    v1_funct_2(k2_funct_1('#skF_6'),k2_relat_1('#skF_6'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_3159,c_100,c_3151,c_4425])).

tff(c_2798,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_6'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2784,c_94])).

tff(c_2802,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_6'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_2798])).

tff(c_2822,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_2802])).

tff(c_4239,plain,(
    ! [C_414,A_415,B_416] :
      ( v1_partfun1(C_414,A_415)
      | ~ v1_funct_2(C_414,A_415,B_416)
      | ~ v1_funct_1(C_414)
      | ~ m1_subset_1(C_414,k1_zfmisc_1(k2_zfmisc_1(A_415,B_416)))
      | v1_xboole_0(B_416) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_4242,plain,
    ( v1_partfun1(k2_funct_1('#skF_6'),k2_relat_1('#skF_6'))
    | ~ v1_funct_2(k2_funct_1('#skF_6'),k2_relat_1('#skF_6'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | v1_xboole_0(k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_4025,c_4239])).

tff(c_4267,plain,
    ( v1_partfun1(k2_funct_1('#skF_6'),k2_relat_1('#skF_6'))
    | ~ v1_funct_2(k2_funct_1('#skF_6'),k2_relat_1('#skF_6'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_2822,c_4242])).

tff(c_4785,plain,(
    v1_partfun1(k2_funct_1('#skF_6'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4385,c_4448,c_4267])).

tff(c_4786,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4415,c_4785])).

tff(c_4787,plain,(
    k1_relat_1(k2_funct_1('#skF_6')) = k2_relat_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_4069])).

tff(c_72,plain,(
    ! [A_53,B_54,C_55] :
      ( k1_relset_1(A_53,B_54,C_55) = k1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_4054,plain,(
    k1_relset_1(k2_relat_1('#skF_6'),k1_relat_1('#skF_6'),k2_funct_1('#skF_6')) = k1_relat_1(k2_funct_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_4025,c_72])).

tff(c_4789,plain,(
    k1_relset_1(k2_relat_1('#skF_6'),k1_relat_1('#skF_6'),k2_funct_1('#skF_6')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4787,c_4054])).

tff(c_4976,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4971,c_4789])).

tff(c_4978,plain,(
    v1_xboole_0(k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_2802])).

tff(c_174,plain,(
    ! [A_94] :
      ( k1_xboole_0 = A_94
      | ~ v1_xboole_0(A_94) ) ),
    inference(resolution,[status(thm)],[c_10,c_165])).

tff(c_5006,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4978,c_174])).

tff(c_5063,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_5006,c_2791])).

tff(c_46,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | ~ m1_subset_1(A_31,k1_zfmisc_1(B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_5086,plain,(
    r1_tarski('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_5063,c_46])).

tff(c_20,plain,(
    ! [A_15] :
      ( k1_xboole_0 = A_15
      | ~ r1_tarski(A_15,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_5109,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_5086,c_20])).

tff(c_5123,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_970,c_5109])).

tff(c_5124,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_967])).

tff(c_5125,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_967])).

tff(c_52,plain,(
    ! [A_36] :
      ( v1_xboole_0(k2_relat_1(A_36))
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_186,plain,(
    ! [A_36] :
      ( k2_relat_1(A_36) = k1_xboole_0
      | ~ v1_xboole_0(A_36) ) ),
    inference(resolution,[status(thm)],[c_52,c_175])).

tff(c_5146,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5124,c_186])).

tff(c_5234,plain,(
    k2_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5125,c_5146])).

tff(c_5467,plain,(
    ! [A_475,B_476,C_477] :
      ( k2_relset_1(A_475,B_476,C_477) = k2_relat_1(C_477)
      | ~ m1_subset_1(C_477,k1_zfmisc_1(k2_zfmisc_1(A_475,B_476))) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_5477,plain,(
    k2_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'),'#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_237,c_5467])).

tff(c_5480,plain,(
    k2_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'),'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5234,c_5477])).

tff(c_5493,plain,(
    k2_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5480,c_160])).

tff(c_5507,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5493,c_94])).

tff(c_5511,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_5124,c_5507])).

tff(c_5513,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_5511])).

tff(c_5514,plain,(
    k2_relset_1(k2_struct_0('#skF_5'),k2_struct_0('#skF_4'),k2_tops_2(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'),'#skF_6')) != k2_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_314])).

tff(c_7982,plain,(
    k2_relset_1(k2_struct_0('#skF_5'),k1_relat_1('#skF_6'),k2_tops_2(k1_relat_1('#skF_6'),k2_struct_0('#skF_5'),'#skF_6')) != k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7977,c_7977,c_7977,c_5514])).

tff(c_8364,plain,(
    k2_relset_1(k2_relat_1('#skF_6'),k1_relat_1('#skF_6'),k2_tops_2(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6')) != k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8358,c_8358,c_7982])).

tff(c_9773,plain,(
    k2_relset_1(k2_relat_1('#skF_6'),k1_relat_1('#skF_6'),k2_funct_1('#skF_6')) != k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9771,c_8364])).

tff(c_6223,plain,(
    ! [A_562] :
      ( k4_relat_1(A_562) = k2_funct_1(A_562)
      | ~ v2_funct_1(A_562)
      | ~ v1_funct_1(A_562)
      | ~ v1_relat_1(A_562) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_6226,plain,
    ( k4_relat_1('#skF_6') = k2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_100,c_6223])).

tff(c_6229,plain,(
    k4_relat_1('#skF_6') = k2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5553,c_108,c_6226])).

tff(c_8072,plain,(
    ! [A_689,B_690,C_691] :
      ( k3_relset_1(A_689,B_690,C_691) = k4_relat_1(C_691)
      | ~ m1_subset_1(C_691,k1_zfmisc_1(k2_zfmisc_1(A_689,B_690))) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_8075,plain,(
    k3_relset_1(k1_relat_1('#skF_6'),k2_struct_0('#skF_5'),'#skF_6') = k4_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_7985,c_8072])).

tff(c_8090,plain,(
    k3_relset_1(k1_relat_1('#skF_6'),k2_struct_0('#skF_5'),'#skF_6') = k2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6229,c_8075])).

tff(c_8367,plain,(
    k3_relset_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6') = k2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8358,c_8090])).

tff(c_9155,plain,(
    ! [A_765,B_766,C_767] :
      ( m1_subset_1(k3_relset_1(A_765,B_766,C_767),k1_zfmisc_1(k2_zfmisc_1(B_766,A_765)))
      | ~ m1_subset_1(C_767,k1_zfmisc_1(k2_zfmisc_1(A_765,B_766))) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_9185,plain,
    ( m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_6'),k1_relat_1('#skF_6'))))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8367,c_9155])).

tff(c_9209,plain,(
    m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_6'),k1_relat_1('#skF_6')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8370,c_9185])).

tff(c_9242,plain,(
    v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_9209,c_64])).

tff(c_9240,plain,(
    v4_relat_1(k2_funct_1('#skF_6'),k2_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_9209,c_68])).

tff(c_9251,plain,
    ( k1_relat_1(k2_funct_1('#skF_6')) = k2_relat_1('#skF_6')
    | ~ v1_partfun1(k2_funct_1('#skF_6'),k2_relat_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_9240,c_84])).

tff(c_9254,plain,
    ( k1_relat_1(k2_funct_1('#skF_6')) = k2_relat_1('#skF_6')
    | ~ v1_partfun1(k2_funct_1('#skF_6'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9242,c_9251])).

tff(c_9503,plain,(
    ~ v1_partfun1(k2_funct_1('#skF_6'),k2_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_9254])).

tff(c_9424,plain,(
    ! [C_771,A_772,B_773] :
      ( v1_funct_1(k2_funct_1(C_771))
      | k2_relset_1(A_772,B_773,C_771) != B_773
      | ~ v2_funct_1(C_771)
      | ~ m1_subset_1(C_771,k1_zfmisc_1(k2_zfmisc_1(A_772,B_773)))
      | ~ v1_funct_2(C_771,A_772,B_773)
      | ~ v1_funct_1(C_771) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_9436,plain,
    ( v1_funct_1(k2_funct_1('#skF_6'))
    | k2_relset_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6') != k2_relat_1('#skF_6')
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),k2_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_8370,c_9424])).

tff(c_9459,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_8372,c_100,c_8363,c_9436])).

tff(c_9504,plain,(
    ! [C_774,B_775,A_776] :
      ( v1_funct_2(k2_funct_1(C_774),B_775,A_776)
      | k2_relset_1(A_776,B_775,C_774) != B_775
      | ~ v2_funct_1(C_774)
      | ~ m1_subset_1(C_774,k1_zfmisc_1(k2_zfmisc_1(A_776,B_775)))
      | ~ v1_funct_2(C_774,A_776,B_775)
      | ~ v1_funct_1(C_774) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_9516,plain,
    ( v1_funct_2(k2_funct_1('#skF_6'),k2_relat_1('#skF_6'),k1_relat_1('#skF_6'))
    | k2_relset_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6') != k2_relat_1('#skF_6')
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),k2_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_8370,c_9504])).

tff(c_9540,plain,(
    v1_funct_2(k2_funct_1('#skF_6'),k2_relat_1('#skF_6'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_8372,c_100,c_8363,c_9516])).

tff(c_7992,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_6'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7977,c_94])).

tff(c_7996,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_6'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_7992])).

tff(c_8016,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_7996])).

tff(c_9304,plain,(
    ! [C_768,A_769,B_770] :
      ( v1_partfun1(C_768,A_769)
      | ~ v1_funct_2(C_768,A_769,B_770)
      | ~ v1_funct_1(C_768)
      | ~ m1_subset_1(C_768,k1_zfmisc_1(k2_zfmisc_1(A_769,B_770)))
      | v1_xboole_0(B_770) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_9307,plain,
    ( v1_partfun1(k2_funct_1('#skF_6'),k2_relat_1('#skF_6'))
    | ~ v1_funct_2(k2_funct_1('#skF_6'),k2_relat_1('#skF_6'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1(k2_funct_1('#skF_6'))
    | v1_xboole_0(k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_9209,c_9304])).

tff(c_9332,plain,
    ( v1_partfun1(k2_funct_1('#skF_6'),k2_relat_1('#skF_6'))
    | ~ v1_funct_2(k2_funct_1('#skF_6'),k2_relat_1('#skF_6'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_8016,c_9307])).

tff(c_9579,plain,(
    v1_partfun1(k2_funct_1('#skF_6'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9459,c_9540,c_9332])).

tff(c_9580,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9503,c_9579])).

tff(c_9581,plain,(
    k1_relat_1(k2_funct_1('#skF_6')) = k2_relat_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_9254])).

tff(c_56,plain,(
    ! [A_39] :
      ( k9_relat_1(A_39,k1_relat_1(A_39)) = k2_relat_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_9590,plain,
    ( k9_relat_1(k2_funct_1('#skF_6'),k2_relat_1('#skF_6')) = k2_relat_1(k2_funct_1('#skF_6'))
    | ~ v1_relat_1(k2_funct_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9581,c_56])).

tff(c_9596,plain,(
    k9_relat_1(k2_funct_1('#skF_6'),k2_relat_1('#skF_6')) = k2_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9242,c_9590])).

tff(c_62,plain,(
    ! [B_43,A_42] :
      ( k9_relat_1(k2_funct_1(B_43),A_42) = k10_relat_1(B_43,A_42)
      | ~ v2_funct_1(B_43)
      | ~ v1_funct_1(B_43)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_9602,plain,
    ( k10_relat_1('#skF_6',k2_relat_1('#skF_6')) = k2_relat_1(k2_funct_1('#skF_6'))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_9596,c_62])).

tff(c_9609,plain,(
    k10_relat_1('#skF_6',k2_relat_1('#skF_6')) = k2_relat_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5553,c_108,c_100,c_9602])).

tff(c_58,plain,(
    ! [A_40] :
      ( k10_relat_1(A_40,k2_relat_1(A_40)) = k1_relat_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_9616,plain,
    ( k2_relat_1(k2_funct_1('#skF_6')) = k1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_9609,c_58])).

tff(c_9623,plain,(
    k2_relat_1(k2_funct_1('#skF_6')) = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5553,c_9616])).

tff(c_74,plain,(
    ! [A_56,B_57,C_58] :
      ( k2_relset_1(A_56,B_57,C_58) = k2_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_9237,plain,(
    k2_relset_1(k2_relat_1('#skF_6'),k1_relat_1('#skF_6'),k2_funct_1('#skF_6')) = k2_relat_1(k2_funct_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_9209,c_74])).

tff(c_9667,plain,(
    k2_relset_1(k2_relat_1('#skF_6'),k1_relat_1('#skF_6'),k2_funct_1('#skF_6')) = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9623,c_9237])).

tff(c_9784,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9773,c_9667])).

tff(c_9786,plain,(
    v1_xboole_0(k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_7996])).

tff(c_9811,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9786,c_174])).

tff(c_9898,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_9811,c_7985])).

tff(c_9921,plain,(
    r1_tarski('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_9898,c_46])).

tff(c_9944,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_9921,c_20])).

tff(c_9958,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6222,c_9944])).

tff(c_9959,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_6219])).

tff(c_9960,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_6219])).

tff(c_189,plain,(
    ! [A_96] :
      ( k2_relat_1(A_96) = k1_xboole_0
      | ~ v1_xboole_0(A_96) ) ),
    inference(resolution,[status(thm)],[c_52,c_175])).

tff(c_201,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_189])).

tff(c_10017,plain,(
    k2_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9960,c_9960,c_201])).

tff(c_10352,plain,(
    ! [A_814,B_815,C_816] :
      ( k2_relset_1(A_814,B_815,C_816) = k2_relat_1(C_816)
      | ~ m1_subset_1(C_816,k1_zfmisc_1(k2_zfmisc_1(A_814,B_815))) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_10362,plain,(
    k2_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'),'#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_237,c_10352])).

tff(c_10365,plain,(
    k2_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'),'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10017,c_10362])).

tff(c_10421,plain,(
    k2_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10365,c_160])).

tff(c_10437,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_10421,c_94])).

tff(c_10441,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_9959,c_10437])).

tff(c_10443,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_10441])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:33:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.27/2.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.54/2.92  
% 8.54/2.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.54/2.92  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k3_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k10_relat_1 > #nlpp > u1_struct_0 > k4_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 8.54/2.92  
% 8.54/2.92  %Foreground sorts:
% 8.54/2.92  
% 8.54/2.92  
% 8.54/2.92  %Background operators:
% 8.54/2.92  
% 8.54/2.92  
% 8.54/2.92  %Foreground operators:
% 8.54/2.92  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.54/2.92  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.54/2.92  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.54/2.92  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.54/2.92  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.54/2.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.54/2.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.54/2.92  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.54/2.92  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.54/2.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.54/2.92  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.54/2.92  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.54/2.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.54/2.92  tff(k3_relset_1, type, k3_relset_1: ($i * $i * $i) > $i).
% 8.54/2.92  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.54/2.92  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 8.54/2.92  tff('#skF_5', type, '#skF_5': $i).
% 8.54/2.92  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.54/2.92  tff('#skF_6', type, '#skF_6': $i).
% 8.54/2.92  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.54/2.92  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.54/2.92  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 8.54/2.92  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.54/2.92  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.54/2.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.54/2.92  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 8.54/2.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.54/2.92  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 8.54/2.92  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.54/2.92  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.54/2.92  tff('#skF_4', type, '#skF_4': $i).
% 8.54/2.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.54/2.92  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.54/2.92  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.54/2.92  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.54/2.92  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.54/2.92  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.54/2.92  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 8.54/2.92  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.54/2.92  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.54/2.92  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 8.54/2.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.54/2.92  
% 8.54/2.95  tff(f_239, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 8.54/2.95  tff(f_195, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 8.54/2.95  tff(f_90, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.54/2.95  tff(f_48, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.54/2.95  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.54/2.95  tff(f_62, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 8.54/2.95  tff(f_36, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.54/2.95  tff(f_83, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 8.54/2.95  tff(f_70, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 8.54/2.95  tff(f_149, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.54/2.95  tff(f_203, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 8.54/2.95  tff(f_103, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.54/2.95  tff(f_97, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.54/2.95  tff(f_137, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.54/2.95  tff(f_175, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 8.54/2.95  tff(f_167, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 8.54/2.95  tff(f_215, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 8.54/2.95  tff(f_119, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 8.54/2.95  tff(f_153, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k3_relset_1(A, B, C) = k4_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_relset_1)).
% 8.54/2.95  tff(f_141, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k3_relset_1(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_relset_1)).
% 8.54/2.95  tff(f_131, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.54/2.95  tff(f_191, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 8.54/2.95  tff(f_145, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.54/2.95  tff(f_52, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 8.54/2.95  tff(f_101, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc11_relat_1)).
% 8.54/2.95  tff(f_107, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 8.54/2.95  tff(f_127, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 8.54/2.95  tff(f_111, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 8.54/2.95  tff(c_112, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_239])).
% 8.54/2.95  tff(c_110, plain, (l1_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_239])).
% 8.54/2.95  tff(c_114, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_239])).
% 8.54/2.95  tff(c_136, plain, (![A_89]: (u1_struct_0(A_89)=k2_struct_0(A_89) | ~l1_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_195])).
% 8.54/2.95  tff(c_144, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_114, c_136])).
% 8.54/2.95  tff(c_143, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_110, c_136])).
% 8.54/2.95  tff(c_104, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_239])).
% 8.54/2.95  tff(c_237, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_143, c_104])).
% 8.54/2.95  tff(c_272, plain, (![A_110, B_111]: (r1_tarski(A_110, B_111) | ~m1_subset_1(A_110, k1_zfmisc_1(B_111)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.54/2.95  tff(c_280, plain, (r1_tarski('#skF_6', k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_237, c_272])).
% 8.54/2.95  tff(c_18, plain, (![A_13, B_14]: (k3_xboole_0(A_13, B_14)=A_13 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.54/2.95  tff(c_5584, plain, (k3_xboole_0('#skF_6', k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5')))='#skF_6'), inference(resolution, [status(thm)], [c_280, c_18])).
% 8.54/2.95  tff(c_8, plain, (![A_5, B_6]: (r1_xboole_0(A_5, B_6) | k3_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.54/2.95  tff(c_5737, plain, (![B_502, A_503]: (~r1_xboole_0(B_502, A_503) | ~r1_tarski(B_502, A_503) | v1_xboole_0(B_502))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.54/2.95  tff(c_6201, plain, (![A_560, B_561]: (~r1_tarski(A_560, B_561) | v1_xboole_0(A_560) | k3_xboole_0(A_560, B_561)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_5737])).
% 8.54/2.95  tff(c_6210, plain, (v1_xboole_0('#skF_6') | k3_xboole_0('#skF_6', k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_280, c_6201])).
% 8.54/2.95  tff(c_6219, plain, (v1_xboole_0('#skF_6') | k1_xboole_0!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_5584, c_6210])).
% 8.54/2.96  tff(c_6222, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_6219])).
% 8.54/2.96  tff(c_10, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.54/2.96  tff(c_42, plain, (![A_28, B_29]: (v1_xboole_0(k2_zfmisc_1(A_28, B_29)) | ~v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.54/2.96  tff(c_165, plain, (![B_93, A_94]: (~v1_xboole_0(B_93) | B_93=A_94 | ~v1_xboole_0(A_94))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.54/2.96  tff(c_175, plain, (![A_95]: (k1_xboole_0=A_95 | ~v1_xboole_0(A_95))), inference(resolution, [status(thm)], [c_10, c_165])).
% 8.54/2.96  tff(c_213, plain, (![A_99, B_100]: (k2_zfmisc_1(A_99, B_100)=k1_xboole_0 | ~v1_xboole_0(A_99))), inference(resolution, [status(thm)], [c_42, c_175])).
% 8.54/2.96  tff(c_222, plain, (![B_100]: (k2_zfmisc_1(k1_xboole_0, B_100)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_213])).
% 8.54/2.96  tff(c_108, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_239])).
% 8.54/2.96  tff(c_6665, plain, (![A_606, B_607, C_608]: (k2_relset_1(A_606, B_607, C_608)=k2_relat_1(C_608) | ~m1_subset_1(C_608, k1_zfmisc_1(k2_zfmisc_1(A_606, B_607))))), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.54/2.96  tff(c_6686, plain, (k2_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5'), '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_237, c_6665])).
% 8.54/2.96  tff(c_102, plain, (k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')=k2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_239])).
% 8.54/2.96  tff(c_160, plain, (k2_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5'), '#skF_6')=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_143, c_102])).
% 8.54/2.96  tff(c_6695, plain, (k2_struct_0('#skF_5')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6686, c_160])).
% 8.54/2.96  tff(c_94, plain, (![A_72]: (~v1_xboole_0(k2_struct_0(A_72)) | ~l1_struct_0(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_203])).
% 8.54/2.96  tff(c_6714, plain, (~v1_xboole_0(k2_relat_1('#skF_6')) | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6695, c_94])).
% 8.54/2.96  tff(c_6718, plain, (~v1_xboole_0(k2_relat_1('#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_6714])).
% 8.54/2.96  tff(c_6719, plain, (~v1_xboole_0(k2_relat_1('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_112, c_6718])).
% 8.54/2.96  tff(c_54, plain, (![A_37, B_38]: (v1_relat_1(k2_zfmisc_1(A_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.54/2.96  tff(c_5543, plain, (![B_482, A_483]: (v1_relat_1(B_482) | ~m1_subset_1(B_482, k1_zfmisc_1(A_483)) | ~v1_relat_1(A_483))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.54/2.96  tff(c_5549, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_237, c_5543])).
% 8.54/2.96  tff(c_5553, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_5549])).
% 8.54/2.96  tff(c_6022, plain, (![C_542, A_543, B_544]: (v4_relat_1(C_542, A_543) | ~m1_subset_1(C_542, k1_zfmisc_1(k2_zfmisc_1(A_543, B_544))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.54/2.96  tff(c_6040, plain, (v4_relat_1('#skF_6', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_237, c_6022])).
% 8.54/2.96  tff(c_6366, plain, (![B_576, A_577]: (k1_relat_1(B_576)=A_577 | ~v1_partfun1(B_576, A_577) | ~v4_relat_1(B_576, A_577) | ~v1_relat_1(B_576))), inference(cnfTransformation, [status(thm)], [f_175])).
% 8.54/2.96  tff(c_6378, plain, (k2_struct_0('#skF_4')=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', k2_struct_0('#skF_4')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_6040, c_6366])).
% 8.54/2.96  tff(c_6388, plain, (k2_struct_0('#skF_4')=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5553, c_6378])).
% 8.54/2.96  tff(c_6395, plain, (~v1_partfun1('#skF_6', k2_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_6388])).
% 8.54/2.96  tff(c_106, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_239])).
% 8.54/2.96  tff(c_146, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_106])).
% 8.54/2.96  tff(c_211, plain, (v1_funct_2('#skF_6', k2_struct_0('#skF_4'), k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_146])).
% 8.54/2.96  tff(c_6709, plain, (v1_funct_2('#skF_6', k2_struct_0('#skF_4'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_6695, c_211])).
% 8.54/2.96  tff(c_6708, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_relat_1('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_6695, c_237])).
% 8.54/2.96  tff(c_7944, plain, (![C_686, A_687, B_688]: (v1_partfun1(C_686, A_687) | ~v1_funct_2(C_686, A_687, B_688) | ~v1_funct_1(C_686) | ~m1_subset_1(C_686, k1_zfmisc_1(k2_zfmisc_1(A_687, B_688))) | v1_xboole_0(B_688))), inference(cnfTransformation, [status(thm)], [f_167])).
% 8.54/2.96  tff(c_7953, plain, (v1_partfun1('#skF_6', k2_struct_0('#skF_4')) | ~v1_funct_2('#skF_6', k2_struct_0('#skF_4'), k2_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | v1_xboole_0(k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_6708, c_7944])).
% 8.54/2.96  tff(c_7974, plain, (v1_partfun1('#skF_6', k2_struct_0('#skF_4')) | v1_xboole_0(k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_6709, c_7953])).
% 8.54/2.96  tff(c_7976, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6719, c_6395, c_7974])).
% 8.54/2.96  tff(c_7977, plain, (k2_struct_0('#skF_4')=k1_relat_1('#skF_6')), inference(splitRight, [status(thm)], [c_6388])).
% 8.54/2.96  tff(c_7985, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_7977, c_237])).
% 8.54/2.96  tff(c_8336, plain, (![A_713, B_714, C_715]: (k2_relset_1(A_713, B_714, C_715)=k2_relat_1(C_715) | ~m1_subset_1(C_715, k1_zfmisc_1(k2_zfmisc_1(A_713, B_714))))), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.54/2.96  tff(c_8356, plain, (k2_relset_1(k1_relat_1('#skF_6'), k2_struct_0('#skF_5'), '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_7985, c_8336])).
% 8.54/2.96  tff(c_7987, plain, (k2_relset_1(k1_relat_1('#skF_6'), k2_struct_0('#skF_5'), '#skF_6')=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7977, c_160])).
% 8.54/2.96  tff(c_8358, plain, (k2_struct_0('#skF_5')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8356, c_7987])).
% 8.54/2.96  tff(c_7986, plain, (v1_funct_2('#skF_6', k1_relat_1('#skF_6'), k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_7977, c_211])).
% 8.54/2.96  tff(c_8372, plain, (v1_funct_2('#skF_6', k1_relat_1('#skF_6'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_8358, c_7986])).
% 8.54/2.96  tff(c_8363, plain, (k2_relset_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8358, c_8356])).
% 8.54/2.96  tff(c_100, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_239])).
% 8.54/2.96  tff(c_8370, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_8358, c_7985])).
% 8.54/2.96  tff(c_9735, plain, (![A_783, B_784, C_785]: (k2_tops_2(A_783, B_784, C_785)=k2_funct_1(C_785) | ~v2_funct_1(C_785) | k2_relset_1(A_783, B_784, C_785)!=B_784 | ~m1_subset_1(C_785, k1_zfmisc_1(k2_zfmisc_1(A_783, B_784))) | ~v1_funct_2(C_785, A_783, B_784) | ~v1_funct_1(C_785))), inference(cnfTransformation, [status(thm)], [f_215])).
% 8.54/2.96  tff(c_9747, plain, (k2_tops_2(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6')=k2_funct_1('#skF_6') | ~v2_funct_1('#skF_6') | k2_relset_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6')!=k2_relat_1('#skF_6') | ~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), k2_relat_1('#skF_6')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_8370, c_9735])).
% 8.54/2.96  tff(c_9771, plain, (k2_tops_2(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6')=k2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_8372, c_8363, c_100, c_9747])).
% 8.54/2.96  tff(c_390, plain, (k3_xboole_0('#skF_6', k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5')))='#skF_6'), inference(resolution, [status(thm)], [c_280, c_18])).
% 8.54/2.96  tff(c_470, plain, (![B_131, A_132]: (~r1_xboole_0(B_131, A_132) | ~r1_tarski(B_131, A_132) | v1_xboole_0(B_131))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.54/2.96  tff(c_949, plain, (![A_190, B_191]: (~r1_tarski(A_190, B_191) | v1_xboole_0(A_190) | k3_xboole_0(A_190, B_191)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_470])).
% 8.54/2.96  tff(c_958, plain, (v1_xboole_0('#skF_6') | k3_xboole_0('#skF_6', k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_280, c_949])).
% 8.54/2.96  tff(c_967, plain, (v1_xboole_0('#skF_6') | k1_xboole_0!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_390, c_958])).
% 8.54/2.96  tff(c_970, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_967])).
% 8.54/2.96  tff(c_1703, plain, (![A_257, B_258, C_259]: (k2_relset_1(A_257, B_258, C_259)=k2_relat_1(C_259) | ~m1_subset_1(C_259, k1_zfmisc_1(k2_zfmisc_1(A_257, B_258))))), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.54/2.96  tff(c_1724, plain, (k2_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5'), '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_237, c_1703])).
% 8.54/2.96  tff(c_1725, plain, (k2_struct_0('#skF_5')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1724, c_160])).
% 8.54/2.96  tff(c_1744, plain, (~v1_xboole_0(k2_relat_1('#skF_6')) | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1725, c_94])).
% 8.54/2.96  tff(c_1748, plain, (~v1_xboole_0(k2_relat_1('#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_1744])).
% 8.54/2.96  tff(c_1749, plain, (~v1_xboole_0(k2_relat_1('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_112, c_1748])).
% 8.54/2.96  tff(c_353, plain, (![B_119, A_120]: (v1_relat_1(B_119) | ~m1_subset_1(B_119, k1_zfmisc_1(A_120)) | ~v1_relat_1(A_120))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.54/2.96  tff(c_359, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_237, c_353])).
% 8.54/2.96  tff(c_363, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_359])).
% 8.54/2.96  tff(c_786, plain, (![C_174, A_175, B_176]: (v4_relat_1(C_174, A_175) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_175, B_176))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.54/2.96  tff(c_801, plain, (v4_relat_1('#skF_6', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_237, c_786])).
% 8.54/2.96  tff(c_1191, plain, (![B_215, A_216]: (k1_relat_1(B_215)=A_216 | ~v1_partfun1(B_215, A_216) | ~v4_relat_1(B_215, A_216) | ~v1_relat_1(B_215))), inference(cnfTransformation, [status(thm)], [f_175])).
% 8.54/2.96  tff(c_1206, plain, (k2_struct_0('#skF_4')=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', k2_struct_0('#skF_4')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_801, c_1191])).
% 8.54/2.96  tff(c_1217, plain, (k2_struct_0('#skF_4')=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_363, c_1206])).
% 8.54/2.96  tff(c_1224, plain, (~v1_partfun1('#skF_6', k2_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_1217])).
% 8.54/2.96  tff(c_1739, plain, (v1_funct_2('#skF_6', k2_struct_0('#skF_4'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1725, c_211])).
% 8.54/2.96  tff(c_1738, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_relat_1('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_1725, c_237])).
% 8.54/2.96  tff(c_2751, plain, (![C_323, A_324, B_325]: (v1_partfun1(C_323, A_324) | ~v1_funct_2(C_323, A_324, B_325) | ~v1_funct_1(C_323) | ~m1_subset_1(C_323, k1_zfmisc_1(k2_zfmisc_1(A_324, B_325))) | v1_xboole_0(B_325))), inference(cnfTransformation, [status(thm)], [f_167])).
% 8.54/2.96  tff(c_2760, plain, (v1_partfun1('#skF_6', k2_struct_0('#skF_4')) | ~v1_funct_2('#skF_6', k2_struct_0('#skF_4'), k2_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | v1_xboole_0(k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_1738, c_2751])).
% 8.54/2.96  tff(c_2781, plain, (v1_partfun1('#skF_6', k2_struct_0('#skF_4')) | v1_xboole_0(k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_1739, c_2760])).
% 8.54/2.96  tff(c_2783, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1749, c_1224, c_2781])).
% 8.54/2.96  tff(c_2784, plain, (k2_struct_0('#skF_4')=k1_relat_1('#skF_6')), inference(splitRight, [status(thm)], [c_1217])).
% 8.54/2.96  tff(c_2791, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_2784, c_237])).
% 8.54/2.96  tff(c_3124, plain, (![A_350, B_351, C_352]: (k2_relset_1(A_350, B_351, C_352)=k2_relat_1(C_352) | ~m1_subset_1(C_352, k1_zfmisc_1(k2_zfmisc_1(A_350, B_351))))), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.54/2.96  tff(c_3144, plain, (k2_relset_1(k1_relat_1('#skF_6'), k2_struct_0('#skF_5'), '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2791, c_3124])).
% 8.54/2.96  tff(c_2793, plain, (k2_relset_1(k1_relat_1('#skF_6'), k2_struct_0('#skF_5'), '#skF_6')=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2784, c_160])).
% 8.54/2.96  tff(c_3146, plain, (k2_struct_0('#skF_5')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3144, c_2793])).
% 8.54/2.96  tff(c_2792, plain, (v1_funct_2('#skF_6', k1_relat_1('#skF_6'), k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2784, c_211])).
% 8.54/2.96  tff(c_3159, plain, (v1_funct_2('#skF_6', k1_relat_1('#skF_6'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_3146, c_2792])).
% 8.54/2.96  tff(c_3151, plain, (k2_relset_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3146, c_3144])).
% 8.54/2.96  tff(c_3157, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_3146, c_2791])).
% 8.54/2.96  tff(c_4937, plain, (![A_450, B_451, C_452]: (k2_tops_2(A_450, B_451, C_452)=k2_funct_1(C_452) | ~v2_funct_1(C_452) | k2_relset_1(A_450, B_451, C_452)!=B_451 | ~m1_subset_1(C_452, k1_zfmisc_1(k2_zfmisc_1(A_450, B_451))) | ~v1_funct_2(C_452, A_450, B_451) | ~v1_funct_1(C_452))), inference(cnfTransformation, [status(thm)], [f_215])).
% 8.54/2.96  tff(c_4946, plain, (k2_tops_2(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6')=k2_funct_1('#skF_6') | ~v2_funct_1('#skF_6') | k2_relset_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6')!=k2_relat_1('#skF_6') | ~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), k2_relat_1('#skF_6')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_3157, c_4937])).
% 8.54/2.96  tff(c_4969, plain, (k2_tops_2(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6')=k2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_3159, c_3151, c_100, c_4946])).
% 8.54/2.96  tff(c_98, plain, (k2_relset_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'))!=k2_struct_0('#skF_4') | k1_relset_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'))!=k2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_239])).
% 8.54/2.96  tff(c_314, plain, (k2_relset_1(k2_struct_0('#skF_5'), k2_struct_0('#skF_4'), k2_tops_2(k2_struct_0('#skF_4'), k2_struct_0('#skF_5'), '#skF_6'))!=k2_struct_0('#skF_4') | k1_relset_1(k2_struct_0('#skF_5'), k2_struct_0('#skF_4'), k2_tops_2(k2_struct_0('#skF_4'), k2_struct_0('#skF_5'), '#skF_6'))!=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_144, c_143, c_143, c_144, c_144, c_143, c_143, c_98])).
% 8.54/2.96  tff(c_315, plain, (k1_relset_1(k2_struct_0('#skF_5'), k2_struct_0('#skF_4'), k2_tops_2(k2_struct_0('#skF_4'), k2_struct_0('#skF_5'), '#skF_6'))!=k2_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_314])).
% 8.54/2.96  tff(c_2789, plain, (k1_relset_1(k2_struct_0('#skF_5'), k1_relat_1('#skF_6'), k2_tops_2(k1_relat_1('#skF_6'), k2_struct_0('#skF_5'), '#skF_6'))!=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2784, c_2784, c_315])).
% 8.54/2.96  tff(c_3155, plain, (k1_relset_1(k2_relat_1('#skF_6'), k1_relat_1('#skF_6'), k2_tops_2(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6'))!=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3146, c_3146, c_3146, c_2789])).
% 8.54/2.96  tff(c_4971, plain, (k1_relset_1(k2_relat_1('#skF_6'), k1_relat_1('#skF_6'), k2_funct_1('#skF_6'))!=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4969, c_3155])).
% 8.54/2.96  tff(c_912, plain, (![A_188]: (k4_relat_1(A_188)=k2_funct_1(A_188) | ~v2_funct_1(A_188) | ~v1_funct_1(A_188) | ~v1_relat_1(A_188))), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.54/2.96  tff(c_915, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_100, c_912])).
% 8.54/2.96  tff(c_918, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_363, c_108, c_915])).
% 8.54/2.96  tff(c_2878, plain, (![A_326, B_327, C_328]: (k3_relset_1(A_326, B_327, C_328)=k4_relat_1(C_328) | ~m1_subset_1(C_328, k1_zfmisc_1(k2_zfmisc_1(A_326, B_327))))), inference(cnfTransformation, [status(thm)], [f_153])).
% 8.54/2.96  tff(c_2881, plain, (k3_relset_1(k1_relat_1('#skF_6'), k2_struct_0('#skF_5'), '#skF_6')=k4_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2791, c_2878])).
% 8.54/2.96  tff(c_2896, plain, (k3_relset_1(k1_relat_1('#skF_6'), k2_struct_0('#skF_5'), '#skF_6')=k2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_918, c_2881])).
% 8.54/2.96  tff(c_3154, plain, (k3_relset_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6')=k2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3146, c_2896])).
% 8.54/2.96  tff(c_3971, plain, (![A_406, B_407, C_408]: (m1_subset_1(k3_relset_1(A_406, B_407, C_408), k1_zfmisc_1(k2_zfmisc_1(B_407, A_406))) | ~m1_subset_1(C_408, k1_zfmisc_1(k2_zfmisc_1(A_406, B_407))))), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.54/2.96  tff(c_4001, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_6'), k1_relat_1('#skF_6')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_3154, c_3971])).
% 8.54/2.96  tff(c_4025, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_6'), k1_relat_1('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_3157, c_4001])).
% 8.54/2.96  tff(c_64, plain, (![C_46, A_44, B_45]: (v1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.54/2.96  tff(c_4058, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_4025, c_64])).
% 8.54/2.96  tff(c_68, plain, (![C_49, A_47, B_48]: (v4_relat_1(C_49, A_47) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.54/2.96  tff(c_4056, plain, (v4_relat_1(k2_funct_1('#skF_6'), k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_4025, c_68])).
% 8.54/2.96  tff(c_84, plain, (![B_67, A_66]: (k1_relat_1(B_67)=A_66 | ~v1_partfun1(B_67, A_66) | ~v4_relat_1(B_67, A_66) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_175])).
% 8.54/2.96  tff(c_4066, plain, (k1_relat_1(k2_funct_1('#skF_6'))=k2_relat_1('#skF_6') | ~v1_partfun1(k2_funct_1('#skF_6'), k2_relat_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_4056, c_84])).
% 8.54/2.96  tff(c_4069, plain, (k1_relat_1(k2_funct_1('#skF_6'))=k2_relat_1('#skF_6') | ~v1_partfun1(k2_funct_1('#skF_6'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_4058, c_4066])).
% 8.54/2.96  tff(c_4415, plain, (~v1_partfun1(k2_funct_1('#skF_6'), k2_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_4069])).
% 8.54/2.96  tff(c_4354, plain, (![C_423, A_424, B_425]: (v1_funct_1(k2_funct_1(C_423)) | k2_relset_1(A_424, B_425, C_423)!=B_425 | ~v2_funct_1(C_423) | ~m1_subset_1(C_423, k1_zfmisc_1(k2_zfmisc_1(A_424, B_425))) | ~v1_funct_2(C_423, A_424, B_425) | ~v1_funct_1(C_423))), inference(cnfTransformation, [status(thm)], [f_191])).
% 8.54/2.96  tff(c_4363, plain, (v1_funct_1(k2_funct_1('#skF_6')) | k2_relset_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6')!=k2_relat_1('#skF_6') | ~v2_funct_1('#skF_6') | ~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), k2_relat_1('#skF_6')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_3157, c_4354])).
% 8.54/2.96  tff(c_4385, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_3159, c_100, c_3151, c_4363])).
% 8.54/2.96  tff(c_4416, plain, (![C_426, B_427, A_428]: (v1_funct_2(k2_funct_1(C_426), B_427, A_428) | k2_relset_1(A_428, B_427, C_426)!=B_427 | ~v2_funct_1(C_426) | ~m1_subset_1(C_426, k1_zfmisc_1(k2_zfmisc_1(A_428, B_427))) | ~v1_funct_2(C_426, A_428, B_427) | ~v1_funct_1(C_426))), inference(cnfTransformation, [status(thm)], [f_191])).
% 8.54/2.96  tff(c_4425, plain, (v1_funct_2(k2_funct_1('#skF_6'), k2_relat_1('#skF_6'), k1_relat_1('#skF_6')) | k2_relset_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6')!=k2_relat_1('#skF_6') | ~v2_funct_1('#skF_6') | ~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), k2_relat_1('#skF_6')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_3157, c_4416])).
% 8.54/2.96  tff(c_4448, plain, (v1_funct_2(k2_funct_1('#skF_6'), k2_relat_1('#skF_6'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_3159, c_100, c_3151, c_4425])).
% 8.54/2.96  tff(c_2798, plain, (~v1_xboole_0(k1_relat_1('#skF_6')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2784, c_94])).
% 8.54/2.96  tff(c_2802, plain, (~v1_xboole_0(k1_relat_1('#skF_6')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_2798])).
% 8.54/2.96  tff(c_2822, plain, (~v1_xboole_0(k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_2802])).
% 8.54/2.96  tff(c_4239, plain, (![C_414, A_415, B_416]: (v1_partfun1(C_414, A_415) | ~v1_funct_2(C_414, A_415, B_416) | ~v1_funct_1(C_414) | ~m1_subset_1(C_414, k1_zfmisc_1(k2_zfmisc_1(A_415, B_416))) | v1_xboole_0(B_416))), inference(cnfTransformation, [status(thm)], [f_167])).
% 8.54/2.96  tff(c_4242, plain, (v1_partfun1(k2_funct_1('#skF_6'), k2_relat_1('#skF_6')) | ~v1_funct_2(k2_funct_1('#skF_6'), k2_relat_1('#skF_6'), k1_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | v1_xboole_0(k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_4025, c_4239])).
% 8.54/2.96  tff(c_4267, plain, (v1_partfun1(k2_funct_1('#skF_6'), k2_relat_1('#skF_6')) | ~v1_funct_2(k2_funct_1('#skF_6'), k2_relat_1('#skF_6'), k1_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_2822, c_4242])).
% 8.54/2.96  tff(c_4785, plain, (v1_partfun1(k2_funct_1('#skF_6'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_4385, c_4448, c_4267])).
% 8.54/2.96  tff(c_4786, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4415, c_4785])).
% 8.54/2.96  tff(c_4787, plain, (k1_relat_1(k2_funct_1('#skF_6'))=k2_relat_1('#skF_6')), inference(splitRight, [status(thm)], [c_4069])).
% 8.54/2.96  tff(c_72, plain, (![A_53, B_54, C_55]: (k1_relset_1(A_53, B_54, C_55)=k1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.54/2.96  tff(c_4054, plain, (k1_relset_1(k2_relat_1('#skF_6'), k1_relat_1('#skF_6'), k2_funct_1('#skF_6'))=k1_relat_1(k2_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_4025, c_72])).
% 8.54/2.96  tff(c_4789, plain, (k1_relset_1(k2_relat_1('#skF_6'), k1_relat_1('#skF_6'), k2_funct_1('#skF_6'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4787, c_4054])).
% 8.54/2.96  tff(c_4976, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4971, c_4789])).
% 8.54/2.96  tff(c_4978, plain, (v1_xboole_0(k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_2802])).
% 8.54/2.96  tff(c_174, plain, (![A_94]: (k1_xboole_0=A_94 | ~v1_xboole_0(A_94))), inference(resolution, [status(thm)], [c_10, c_165])).
% 8.54/2.96  tff(c_5006, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_4978, c_174])).
% 8.54/2.96  tff(c_5063, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_222, c_5006, c_2791])).
% 8.54/2.96  tff(c_46, plain, (![A_31, B_32]: (r1_tarski(A_31, B_32) | ~m1_subset_1(A_31, k1_zfmisc_1(B_32)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.54/2.96  tff(c_5086, plain, (r1_tarski('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_5063, c_46])).
% 8.54/2.96  tff(c_20, plain, (![A_15]: (k1_xboole_0=A_15 | ~r1_tarski(A_15, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.54/2.96  tff(c_5109, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_5086, c_20])).
% 8.54/2.96  tff(c_5123, plain, $false, inference(negUnitSimplification, [status(thm)], [c_970, c_5109])).
% 8.54/2.96  tff(c_5124, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_967])).
% 8.54/2.96  tff(c_5125, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_967])).
% 8.54/2.96  tff(c_52, plain, (![A_36]: (v1_xboole_0(k2_relat_1(A_36)) | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.54/2.96  tff(c_186, plain, (![A_36]: (k2_relat_1(A_36)=k1_xboole_0 | ~v1_xboole_0(A_36))), inference(resolution, [status(thm)], [c_52, c_175])).
% 8.54/2.96  tff(c_5146, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_5124, c_186])).
% 8.54/2.96  tff(c_5234, plain, (k2_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_5125, c_5146])).
% 8.54/2.96  tff(c_5467, plain, (![A_475, B_476, C_477]: (k2_relset_1(A_475, B_476, C_477)=k2_relat_1(C_477) | ~m1_subset_1(C_477, k1_zfmisc_1(k2_zfmisc_1(A_475, B_476))))), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.54/2.96  tff(c_5477, plain, (k2_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5'), '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_237, c_5467])).
% 8.54/2.96  tff(c_5480, plain, (k2_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5'), '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_5234, c_5477])).
% 8.54/2.96  tff(c_5493, plain, (k2_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_5480, c_160])).
% 8.54/2.96  tff(c_5507, plain, (~v1_xboole_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5493, c_94])).
% 8.54/2.96  tff(c_5511, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_5124, c_5507])).
% 8.54/2.96  tff(c_5513, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_5511])).
% 8.54/2.96  tff(c_5514, plain, (k2_relset_1(k2_struct_0('#skF_5'), k2_struct_0('#skF_4'), k2_tops_2(k2_struct_0('#skF_4'), k2_struct_0('#skF_5'), '#skF_6'))!=k2_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_314])).
% 8.54/2.96  tff(c_7982, plain, (k2_relset_1(k2_struct_0('#skF_5'), k1_relat_1('#skF_6'), k2_tops_2(k1_relat_1('#skF_6'), k2_struct_0('#skF_5'), '#skF_6'))!=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7977, c_7977, c_7977, c_5514])).
% 8.54/2.96  tff(c_8364, plain, (k2_relset_1(k2_relat_1('#skF_6'), k1_relat_1('#skF_6'), k2_tops_2(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6'))!=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8358, c_8358, c_7982])).
% 8.54/2.96  tff(c_9773, plain, (k2_relset_1(k2_relat_1('#skF_6'), k1_relat_1('#skF_6'), k2_funct_1('#skF_6'))!=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_9771, c_8364])).
% 8.54/2.96  tff(c_6223, plain, (![A_562]: (k4_relat_1(A_562)=k2_funct_1(A_562) | ~v2_funct_1(A_562) | ~v1_funct_1(A_562) | ~v1_relat_1(A_562))), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.54/2.96  tff(c_6226, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_100, c_6223])).
% 8.54/2.96  tff(c_6229, plain, (k4_relat_1('#skF_6')=k2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5553, c_108, c_6226])).
% 8.54/2.96  tff(c_8072, plain, (![A_689, B_690, C_691]: (k3_relset_1(A_689, B_690, C_691)=k4_relat_1(C_691) | ~m1_subset_1(C_691, k1_zfmisc_1(k2_zfmisc_1(A_689, B_690))))), inference(cnfTransformation, [status(thm)], [f_153])).
% 8.54/2.96  tff(c_8075, plain, (k3_relset_1(k1_relat_1('#skF_6'), k2_struct_0('#skF_5'), '#skF_6')=k4_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_7985, c_8072])).
% 8.54/2.96  tff(c_8090, plain, (k3_relset_1(k1_relat_1('#skF_6'), k2_struct_0('#skF_5'), '#skF_6')=k2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6229, c_8075])).
% 8.54/2.96  tff(c_8367, plain, (k3_relset_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6')=k2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8358, c_8090])).
% 8.54/2.96  tff(c_9155, plain, (![A_765, B_766, C_767]: (m1_subset_1(k3_relset_1(A_765, B_766, C_767), k1_zfmisc_1(k2_zfmisc_1(B_766, A_765))) | ~m1_subset_1(C_767, k1_zfmisc_1(k2_zfmisc_1(A_765, B_766))))), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.54/2.96  tff(c_9185, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_6'), k1_relat_1('#skF_6')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_8367, c_9155])).
% 8.54/2.96  tff(c_9209, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_6'), k1_relat_1('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_8370, c_9185])).
% 8.54/2.96  tff(c_9242, plain, (v1_relat_1(k2_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_9209, c_64])).
% 8.54/2.96  tff(c_9240, plain, (v4_relat_1(k2_funct_1('#skF_6'), k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_9209, c_68])).
% 8.54/2.96  tff(c_9251, plain, (k1_relat_1(k2_funct_1('#skF_6'))=k2_relat_1('#skF_6') | ~v1_partfun1(k2_funct_1('#skF_6'), k2_relat_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_9240, c_84])).
% 8.54/2.96  tff(c_9254, plain, (k1_relat_1(k2_funct_1('#skF_6'))=k2_relat_1('#skF_6') | ~v1_partfun1(k2_funct_1('#skF_6'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_9242, c_9251])).
% 8.54/2.96  tff(c_9503, plain, (~v1_partfun1(k2_funct_1('#skF_6'), k2_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_9254])).
% 8.54/2.96  tff(c_9424, plain, (![C_771, A_772, B_773]: (v1_funct_1(k2_funct_1(C_771)) | k2_relset_1(A_772, B_773, C_771)!=B_773 | ~v2_funct_1(C_771) | ~m1_subset_1(C_771, k1_zfmisc_1(k2_zfmisc_1(A_772, B_773))) | ~v1_funct_2(C_771, A_772, B_773) | ~v1_funct_1(C_771))), inference(cnfTransformation, [status(thm)], [f_191])).
% 8.54/2.96  tff(c_9436, plain, (v1_funct_1(k2_funct_1('#skF_6')) | k2_relset_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6')!=k2_relat_1('#skF_6') | ~v2_funct_1('#skF_6') | ~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), k2_relat_1('#skF_6')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_8370, c_9424])).
% 8.54/2.96  tff(c_9459, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_8372, c_100, c_8363, c_9436])).
% 8.54/2.96  tff(c_9504, plain, (![C_774, B_775, A_776]: (v1_funct_2(k2_funct_1(C_774), B_775, A_776) | k2_relset_1(A_776, B_775, C_774)!=B_775 | ~v2_funct_1(C_774) | ~m1_subset_1(C_774, k1_zfmisc_1(k2_zfmisc_1(A_776, B_775))) | ~v1_funct_2(C_774, A_776, B_775) | ~v1_funct_1(C_774))), inference(cnfTransformation, [status(thm)], [f_191])).
% 8.54/2.96  tff(c_9516, plain, (v1_funct_2(k2_funct_1('#skF_6'), k2_relat_1('#skF_6'), k1_relat_1('#skF_6')) | k2_relset_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6')!=k2_relat_1('#skF_6') | ~v2_funct_1('#skF_6') | ~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), k2_relat_1('#skF_6')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_8370, c_9504])).
% 8.54/2.96  tff(c_9540, plain, (v1_funct_2(k2_funct_1('#skF_6'), k2_relat_1('#skF_6'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_8372, c_100, c_8363, c_9516])).
% 8.54/2.96  tff(c_7992, plain, (~v1_xboole_0(k1_relat_1('#skF_6')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7977, c_94])).
% 8.54/2.96  tff(c_7996, plain, (~v1_xboole_0(k1_relat_1('#skF_6')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_7992])).
% 8.54/2.96  tff(c_8016, plain, (~v1_xboole_0(k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_7996])).
% 8.54/2.96  tff(c_9304, plain, (![C_768, A_769, B_770]: (v1_partfun1(C_768, A_769) | ~v1_funct_2(C_768, A_769, B_770) | ~v1_funct_1(C_768) | ~m1_subset_1(C_768, k1_zfmisc_1(k2_zfmisc_1(A_769, B_770))) | v1_xboole_0(B_770))), inference(cnfTransformation, [status(thm)], [f_167])).
% 8.54/2.96  tff(c_9307, plain, (v1_partfun1(k2_funct_1('#skF_6'), k2_relat_1('#skF_6')) | ~v1_funct_2(k2_funct_1('#skF_6'), k2_relat_1('#skF_6'), k1_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6')) | v1_xboole_0(k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_9209, c_9304])).
% 8.54/2.96  tff(c_9332, plain, (v1_partfun1(k2_funct_1('#skF_6'), k2_relat_1('#skF_6')) | ~v1_funct_2(k2_funct_1('#skF_6'), k2_relat_1('#skF_6'), k1_relat_1('#skF_6')) | ~v1_funct_1(k2_funct_1('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_8016, c_9307])).
% 8.54/2.96  tff(c_9579, plain, (v1_partfun1(k2_funct_1('#skF_6'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_9459, c_9540, c_9332])).
% 8.54/2.96  tff(c_9580, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9503, c_9579])).
% 8.54/2.96  tff(c_9581, plain, (k1_relat_1(k2_funct_1('#skF_6'))=k2_relat_1('#skF_6')), inference(splitRight, [status(thm)], [c_9254])).
% 8.54/2.96  tff(c_56, plain, (![A_39]: (k9_relat_1(A_39, k1_relat_1(A_39))=k2_relat_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.54/2.96  tff(c_9590, plain, (k9_relat_1(k2_funct_1('#skF_6'), k2_relat_1('#skF_6'))=k2_relat_1(k2_funct_1('#skF_6')) | ~v1_relat_1(k2_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_9581, c_56])).
% 8.54/2.96  tff(c_9596, plain, (k9_relat_1(k2_funct_1('#skF_6'), k2_relat_1('#skF_6'))=k2_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_9242, c_9590])).
% 8.54/2.96  tff(c_62, plain, (![B_43, A_42]: (k9_relat_1(k2_funct_1(B_43), A_42)=k10_relat_1(B_43, A_42) | ~v2_funct_1(B_43) | ~v1_funct_1(B_43) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.54/2.96  tff(c_9602, plain, (k10_relat_1('#skF_6', k2_relat_1('#skF_6'))=k2_relat_1(k2_funct_1('#skF_6')) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_9596, c_62])).
% 8.54/2.96  tff(c_9609, plain, (k10_relat_1('#skF_6', k2_relat_1('#skF_6'))=k2_relat_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_5553, c_108, c_100, c_9602])).
% 8.54/2.96  tff(c_58, plain, (![A_40]: (k10_relat_1(A_40, k2_relat_1(A_40))=k1_relat_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.54/2.96  tff(c_9616, plain, (k2_relat_1(k2_funct_1('#skF_6'))=k1_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_9609, c_58])).
% 8.54/2.96  tff(c_9623, plain, (k2_relat_1(k2_funct_1('#skF_6'))=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5553, c_9616])).
% 8.54/2.96  tff(c_74, plain, (![A_56, B_57, C_58]: (k2_relset_1(A_56, B_57, C_58)=k2_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.54/2.96  tff(c_9237, plain, (k2_relset_1(k2_relat_1('#skF_6'), k1_relat_1('#skF_6'), k2_funct_1('#skF_6'))=k2_relat_1(k2_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_9209, c_74])).
% 8.54/2.96  tff(c_9667, plain, (k2_relset_1(k2_relat_1('#skF_6'), k1_relat_1('#skF_6'), k2_funct_1('#skF_6'))=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_9623, c_9237])).
% 8.54/2.96  tff(c_9784, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9773, c_9667])).
% 8.54/2.96  tff(c_9786, plain, (v1_xboole_0(k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_7996])).
% 8.54/2.96  tff(c_9811, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_9786, c_174])).
% 8.54/2.96  tff(c_9898, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_222, c_9811, c_7985])).
% 8.54/2.96  tff(c_9921, plain, (r1_tarski('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_9898, c_46])).
% 8.54/2.96  tff(c_9944, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_9921, c_20])).
% 8.54/2.96  tff(c_9958, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6222, c_9944])).
% 8.54/2.96  tff(c_9959, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_6219])).
% 8.54/2.96  tff(c_9960, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_6219])).
% 8.54/2.96  tff(c_189, plain, (![A_96]: (k2_relat_1(A_96)=k1_xboole_0 | ~v1_xboole_0(A_96))), inference(resolution, [status(thm)], [c_52, c_175])).
% 8.54/2.96  tff(c_201, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_189])).
% 8.54/2.96  tff(c_10017, plain, (k2_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_9960, c_9960, c_201])).
% 8.54/2.96  tff(c_10352, plain, (![A_814, B_815, C_816]: (k2_relset_1(A_814, B_815, C_816)=k2_relat_1(C_816) | ~m1_subset_1(C_816, k1_zfmisc_1(k2_zfmisc_1(A_814, B_815))))), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.54/2.96  tff(c_10362, plain, (k2_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5'), '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_237, c_10352])).
% 8.54/2.96  tff(c_10365, plain, (k2_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5'), '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_10017, c_10362])).
% 8.54/2.96  tff(c_10421, plain, (k2_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_10365, c_160])).
% 8.54/2.96  tff(c_10437, plain, (~v1_xboole_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_10421, c_94])).
% 8.54/2.96  tff(c_10441, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_9959, c_10437])).
% 8.54/2.96  tff(c_10443, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_10441])).
% 8.54/2.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.54/2.96  
% 8.54/2.96  Inference rules
% 8.54/2.96  ----------------------
% 8.54/2.96  #Ref     : 0
% 8.54/2.96  #Sup     : 2520
% 8.54/2.96  #Fact    : 0
% 8.54/2.96  #Define  : 0
% 8.54/2.96  #Split   : 24
% 8.54/2.96  #Chain   : 0
% 8.54/2.96  #Close   : 0
% 8.54/2.96  
% 8.54/2.96  Ordering : KBO
% 8.54/2.96  
% 8.54/2.96  Simplification rules
% 8.54/2.96  ----------------------
% 8.54/2.96  #Subsume      : 291
% 8.54/2.96  #Demod        : 1467
% 8.54/2.96  #Tautology    : 1055
% 8.54/2.96  #SimpNegUnit  : 63
% 8.54/2.96  #BackRed      : 222
% 8.54/2.96  
% 8.54/2.96  #Partial instantiations: 0
% 8.54/2.96  #Strategies tried      : 1
% 8.54/2.96  
% 8.54/2.96  Timing (in seconds)
% 8.54/2.96  ----------------------
% 8.54/2.96  Preprocessing        : 0.38
% 8.54/2.96  Parsing              : 0.19
% 8.54/2.96  CNF conversion       : 0.03
% 8.54/2.96  Main loop            : 1.77
% 8.54/2.96  Inferencing          : 0.57
% 8.54/2.96  Reduction            : 0.63
% 8.54/2.96  Demodulation         : 0.44
% 8.54/2.96  BG Simplification    : 0.06
% 8.54/2.96  Subsumption          : 0.35
% 8.54/2.96  Abstraction          : 0.07
% 8.54/2.96  MUC search           : 0.00
% 8.54/2.96  Cooper               : 0.00
% 8.54/2.96  Total                : 2.24
% 8.54/2.96  Index Insertion      : 0.00
% 8.54/2.96  Index Deletion       : 0.00
% 8.54/2.96  Index Matching       : 0.00
% 8.54/2.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
