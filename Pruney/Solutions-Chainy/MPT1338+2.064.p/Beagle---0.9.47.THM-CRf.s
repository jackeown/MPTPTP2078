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
% DateTime   : Thu Dec  3 10:23:23 EST 2020

% Result     : Theorem 7.84s
% Output     : CNFRefutation 8.42s
% Verified   : 
% Statistics : Number of formulae       :  330 (15639 expanded)
%              Number of leaves         :   55 (5420 expanded)
%              Depth                    :   29
%              Number of atoms          :  577 (46305 expanded)
%              Number of equality atoms :  173 (14401 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k3_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k4_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_relset_1,type,(
    k3_relset_1: ( $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_198,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_154,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_134,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_126,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k3_relset_1(A,B,C) = k4_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k3_relset_1(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v2_funct_1(A)
            & r1_tarski(B,k1_relat_1(A)) )
         => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_174,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_150,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_162,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_76,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_18,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_80,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_112,plain,(
    ! [A_65] :
      ( u1_struct_0(A_65) = k2_struct_0(A_65)
      | ~ l1_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_120,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_112])).

tff(c_119,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_112])).

tff(c_70,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_132,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_119,c_70])).

tff(c_156,plain,(
    ! [B_71,A_72] :
      ( v1_relat_1(B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_72))
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_159,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_132,c_156])).

tff(c_162,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_159])).

tff(c_74,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_66,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_8,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6389,plain,(
    ! [A_683,B_684,C_685] :
      ( k2_relset_1(A_683,B_684,C_685) = k2_relat_1(C_685)
      | ~ m1_subset_1(C_685,k1_zfmisc_1(k2_zfmisc_1(A_683,B_684))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_6399,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_132,c_6389])).

tff(c_68,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_140,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_119,c_68])).

tff(c_6400,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6399,c_140])).

tff(c_4574,plain,(
    ! [C_508,B_509,A_510] :
      ( v1_xboole_0(C_508)
      | ~ m1_subset_1(C_508,k1_zfmisc_1(k2_zfmisc_1(B_509,A_510)))
      | ~ v1_xboole_0(A_510) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_4584,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_132,c_4574])).

tff(c_4585,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_4584])).

tff(c_6407,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6400,c_4585])).

tff(c_163,plain,(
    ! [C_73,A_74,B_75] :
      ( v4_relat_1(C_73,A_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_173,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_132,c_163])).

tff(c_6364,plain,(
    ! [B_676,A_677] :
      ( k1_relat_1(B_676) = A_677
      | ~ v1_partfun1(B_676,A_677)
      | ~ v4_relat_1(B_676,A_677)
      | ~ v1_relat_1(B_676) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_6367,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_173,c_6364])).

tff(c_6370,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_6367])).

tff(c_6371,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_6370])).

tff(c_72,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_121,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_72])).

tff(c_131,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_121])).

tff(c_6412,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6400,c_131])).

tff(c_6411,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6400,c_132])).

tff(c_6746,plain,(
    ! [C_724,A_725,B_726] :
      ( v1_partfun1(C_724,A_725)
      | ~ v1_funct_2(C_724,A_725,B_726)
      | ~ v1_funct_1(C_724)
      | ~ m1_subset_1(C_724,k1_zfmisc_1(k2_zfmisc_1(A_725,B_726)))
      | v1_xboole_0(B_726) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_6759,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6411,c_6746])).

tff(c_6773,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_6412,c_6759])).

tff(c_6775,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6407,c_6371,c_6773])).

tff(c_6776,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_6370])).

tff(c_6784,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6776,c_132])).

tff(c_40,plain,(
    ! [A_35,B_36,C_37] :
      ( k2_relset_1(A_35,B_36,C_37) = k2_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_6858,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6784,c_40])).

tff(c_6783,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6776,c_140])).

tff(c_6871,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6858,c_6783])).

tff(c_6877,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6871,c_6784])).

tff(c_4563,plain,(
    ! [A_507] :
      ( k4_relat_1(A_507) = k2_funct_1(A_507)
      | ~ v2_funct_1(A_507)
      | ~ v1_funct_1(A_507)
      | ~ v1_relat_1(A_507) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4566,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_4563])).

tff(c_4569,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_74,c_4566])).

tff(c_42,plain,(
    ! [A_38,B_39,C_40] :
      ( k3_relset_1(A_38,B_39,C_40) = k4_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_6905,plain,(
    k3_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6877,c_42])).

tff(c_6922,plain,(
    k3_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4569,c_6905])).

tff(c_7064,plain,(
    ! [A_753,B_754,C_755] :
      ( m1_subset_1(k3_relset_1(A_753,B_754,C_755),k1_zfmisc_1(k2_zfmisc_1(B_754,A_753)))
      | ~ m1_subset_1(C_755,k1_zfmisc_1(k2_zfmisc_1(A_753,B_754))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_7088,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6922,c_7064])).

tff(c_7105,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6877,c_7088])).

tff(c_16,plain,(
    ! [B_8,A_6] :
      ( v1_relat_1(B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_6))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_7128,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_7105,c_16])).

tff(c_7137,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_7128])).

tff(c_30,plain,(
    ! [C_21,A_19,B_20] :
      ( v4_relat_1(C_21,A_19)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_7134,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_7105,c_30])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( k7_relat_1(B_14,A_13) = B_14
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_7143,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_7134,c_22])).

tff(c_7149,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7137,c_7143])).

tff(c_20,plain,(
    ! [B_12,A_11] :
      ( k2_relat_1(k7_relat_1(B_12,A_11)) = k9_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_7153,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7149,c_20])).

tff(c_7157,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7137,c_7153])).

tff(c_4543,plain,(
    ! [B_505,A_506] :
      ( k7_relat_1(B_505,A_506) = B_505
      | ~ v4_relat_1(B_505,A_506)
      | ~ v1_relat_1(B_505) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4546,plain,
    ( k7_relat_1('#skF_3',k2_struct_0('#skF_1')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_173,c_4543])).

tff(c_4549,plain,(
    k7_relat_1('#skF_3',k2_struct_0('#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_4546])).

tff(c_4553,plain,
    ( k9_relat_1('#skF_3',k2_struct_0('#skF_1')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4549,c_20])).

tff(c_4557,plain,(
    k9_relat_1('#skF_3',k2_struct_0('#skF_1')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_4553])).

tff(c_6779,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6776,c_4557])).

tff(c_7187,plain,(
    ! [A_762,B_763] :
      ( k9_relat_1(k2_funct_1(A_762),k9_relat_1(A_762,B_763)) = B_763
      | ~ r1_tarski(B_763,k1_relat_1(A_762))
      | ~ v2_funct_1(A_762)
      | ~ v1_funct_1(A_762)
      | ~ v1_relat_1(A_762) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_7205,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6779,c_7187])).

tff(c_7211,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_74,c_66,c_8,c_7157,c_7205])).

tff(c_7131,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_7105,c_40])).

tff(c_7230,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7211,c_7131])).

tff(c_6785,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6776,c_131])).

tff(c_6878,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6871,c_6785])).

tff(c_6876,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6871,c_6858])).

tff(c_7903,plain,(
    ! [A_836,B_837,C_838] :
      ( k2_tops_2(A_836,B_837,C_838) = k2_funct_1(C_838)
      | ~ v2_funct_1(C_838)
      | k2_relset_1(A_836,B_837,C_838) != B_837
      | ~ m1_subset_1(C_838,k1_zfmisc_1(k2_zfmisc_1(A_836,B_837)))
      | ~ v1_funct_2(C_838,A_836,B_837)
      | ~ v1_funct_1(C_838) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_7919,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6877,c_7903])).

tff(c_7934,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_6878,c_6876,c_66,c_7919])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2087,plain,(
    ! [A_289,B_290,C_291] :
      ( k2_relset_1(A_289,B_290,C_291) = k2_relat_1(C_291)
      | ~ m1_subset_1(C_291,k1_zfmisc_1(k2_zfmisc_1(A_289,B_290))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2097,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_132,c_2087])).

tff(c_2098,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2097,c_140])).

tff(c_229,plain,(
    ! [C_88,B_89,A_90] :
      ( v1_xboole_0(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(B_89,A_90)))
      | ~ v1_xboole_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_239,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_132,c_229])).

tff(c_240,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_239])).

tff(c_2107,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2098,c_240])).

tff(c_2047,plain,(
    ! [B_279,A_280] :
      ( k1_relat_1(B_279) = A_280
      | ~ v1_partfun1(B_279,A_280)
      | ~ v4_relat_1(B_279,A_280)
      | ~ v1_relat_1(B_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2050,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_173,c_2047])).

tff(c_2053,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_2050])).

tff(c_2054,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_2053])).

tff(c_2110,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2098,c_131])).

tff(c_2109,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2098,c_132])).

tff(c_2402,plain,(
    ! [C_308,A_309,B_310] :
      ( v1_partfun1(C_308,A_309)
      | ~ v1_funct_2(C_308,A_309,B_310)
      | ~ v1_funct_1(C_308)
      | ~ m1_subset_1(C_308,k1_zfmisc_1(k2_zfmisc_1(A_309,B_310)))
      | v1_xboole_0(B_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2411,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2109,c_2402])).

tff(c_2428,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2110,c_2411])).

tff(c_2430,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2107,c_2054,c_2428])).

tff(c_2431,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2053])).

tff(c_2438,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2431,c_132])).

tff(c_2547,plain,(
    ! [A_321,B_322,C_323] :
      ( k2_relset_1(A_321,B_322,C_323) = k2_relat_1(C_323)
      | ~ m1_subset_1(C_323,k1_zfmisc_1(k2_zfmisc_1(A_321,B_322))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2557,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2438,c_2547])).

tff(c_2437,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2431,c_140])).

tff(c_2558,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2557,c_2437])).

tff(c_2566,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2558,c_2438])).

tff(c_214,plain,(
    ! [A_87] :
      ( k4_relat_1(A_87) = k2_funct_1(A_87)
      | ~ v2_funct_1(A_87)
      | ~ v1_funct_1(A_87)
      | ~ v1_relat_1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_217,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_214])).

tff(c_220,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_74,c_217])).

tff(c_2531,plain,(
    ! [A_318,B_319,C_320] :
      ( k3_relset_1(A_318,B_319,C_320) = k4_relat_1(C_320)
      | ~ m1_subset_1(C_320,k1_zfmisc_1(k2_zfmisc_1(A_318,B_319))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2534,plain,(
    k3_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2438,c_2531])).

tff(c_2542,plain,(
    k3_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_2534])).

tff(c_2564,plain,(
    k3_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2558,c_2542])).

tff(c_2716,plain,(
    ! [A_331,B_332,C_333] :
      ( m1_subset_1(k3_relset_1(A_331,B_332,C_333),k1_zfmisc_1(k2_zfmisc_1(B_332,A_331)))
      | ~ m1_subset_1(C_333,k1_zfmisc_1(k2_zfmisc_1(A_331,B_332))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2740,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2564,c_2716])).

tff(c_2757,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2566,c_2740])).

tff(c_2780,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_2757,c_16])).

tff(c_2789,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2780])).

tff(c_2786,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2757,c_30])).

tff(c_50,plain,(
    ! [B_46,A_45] :
      ( k1_relat_1(B_46) = A_45
      | ~ v1_partfun1(B_46,A_45)
      | ~ v4_relat_1(B_46,A_45)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2792,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2786,c_50])).

tff(c_2798,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2789,c_2792])).

tff(c_2914,plain,(
    ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2798])).

tff(c_2439,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2431,c_131])).

tff(c_2567,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2558,c_2439])).

tff(c_2563,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2558,c_2557])).

tff(c_3011,plain,(
    ! [C_351,A_352,B_353] :
      ( v1_funct_1(k2_funct_1(C_351))
      | k2_relset_1(A_352,B_353,C_351) != B_353
      | ~ v2_funct_1(C_351)
      | ~ m1_subset_1(C_351,k1_zfmisc_1(k2_zfmisc_1(A_352,B_353)))
      | ~ v1_funct_2(C_351,A_352,B_353)
      | ~ v1_funct_1(C_351) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_3027,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2566,c_3011])).

tff(c_3042,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2567,c_66,c_2563,c_3027])).

tff(c_60,plain,(
    ! [A_51] :
      ( ~ v1_xboole_0(k2_struct_0(A_51))
      | ~ l1_struct_0(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_2444,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2431,c_60])).

tff(c_2448,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_3'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2444])).

tff(c_2484,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2448])).

tff(c_2915,plain,(
    ! [C_348,A_349,B_350] :
      ( v1_partfun1(C_348,A_349)
      | ~ v1_funct_2(C_348,A_349,B_350)
      | ~ v1_funct_1(C_348)
      | ~ m1_subset_1(C_348,k1_zfmisc_1(k2_zfmisc_1(A_349,B_350)))
      | v1_xboole_0(B_350) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2918,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2757,c_2915])).

tff(c_2937,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_2484,c_2918])).

tff(c_3080,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3042,c_2937])).

tff(c_3081,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_2914,c_3080])).

tff(c_3155,plain,(
    ! [C_368,B_369,A_370] :
      ( v1_funct_2(k2_funct_1(C_368),B_369,A_370)
      | k2_relset_1(A_370,B_369,C_368) != B_369
      | ~ v2_funct_1(C_368)
      | ~ m1_subset_1(C_368,k1_zfmisc_1(k2_zfmisc_1(A_370,B_369)))
      | ~ v1_funct_2(C_368,A_370,B_369)
      | ~ v1_funct_1(C_368) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_3171,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2566,c_3155])).

tff(c_3186,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2567,c_66,c_2563,c_3171])).

tff(c_3188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3081,c_3186])).

tff(c_3189,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2798])).

tff(c_38,plain,(
    ! [A_32,B_33,C_34] :
      ( k1_relset_1(A_32,B_33,C_34) = k1_relat_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2783,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2757,c_38])).

tff(c_3191,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3189,c_2783])).

tff(c_3711,plain,(
    ! [A_434,B_435,C_436] :
      ( k2_tops_2(A_434,B_435,C_436) = k2_funct_1(C_436)
      | ~ v2_funct_1(C_436)
      | k2_relset_1(A_434,B_435,C_436) != B_435
      | ~ m1_subset_1(C_436,k1_zfmisc_1(k2_zfmisc_1(A_434,B_435)))
      | ~ v1_funct_2(C_436,A_434,B_435)
      | ~ v1_funct_1(C_436) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_3727,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2566,c_3711])).

tff(c_3743,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2567,c_2563,c_66,c_3727])).

tff(c_64,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_187,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_120,c_119,c_119,c_120,c_120,c_119,c_119,c_64])).

tff(c_188,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_2433,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2431,c_2431,c_188])).

tff(c_2700,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2558,c_2558,c_2558,c_2433])).

tff(c_3744,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3743,c_2700])).

tff(c_3747,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3191,c_3744])).

tff(c_3749,plain,(
    v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2448])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3753,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3749,c_2])).

tff(c_3774,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3753,c_2438])).

tff(c_3781,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_3774])).

tff(c_246,plain,(
    ! [B_93,A_94] :
      ( k1_relat_1(B_93) = A_94
      | ~ v1_partfun1(B_93,A_94)
      | ~ v4_relat_1(B_93,A_94)
      | ~ v1_relat_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_249,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_173,c_246])).

tff(c_252,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_249])).

tff(c_253,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_252])).

tff(c_271,plain,(
    ! [A_102,B_103,C_104] :
      ( k2_relset_1(A_102,B_103,C_104) = k2_relat_1(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_281,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_132,c_271])).

tff(c_282,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_140])).

tff(c_291,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_131])).

tff(c_290,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_132])).

tff(c_238,plain,(
    ! [C_88,B_5] :
      ( v1_xboole_0(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(B_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_229])).

tff(c_241,plain,(
    ! [B_5] : ~ v1_xboole_0(B_5) ),
    inference(splitLeft,[status(thm)],[c_238])).

tff(c_44,plain,(
    ! [C_44,A_41,B_42] :
      ( v1_partfun1(C_44,A_41)
      | ~ v1_funct_2(C_44,A_41,B_42)
      | ~ v1_funct_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42)))
      | v1_xboole_0(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_588,plain,(
    ! [C_133,A_134,B_135] :
      ( v1_partfun1(C_133,A_134)
      | ~ v1_funct_2(C_133,A_134,B_135)
      | ~ v1_funct_1(C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_241,c_44])).

tff(c_601,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_290,c_588])).

tff(c_613,plain,(
    v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_291,c_601])).

tff(c_615,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_253,c_613])).

tff(c_616,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_622,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_132])).

tff(c_706,plain,(
    ! [A_143,B_144,C_145] :
      ( k2_relset_1(A_143,B_144,C_145) = k2_relat_1(C_145)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_716,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_622,c_706])).

tff(c_621,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_140])).

tff(c_717,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_716,c_621])).

tff(c_725,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_717,c_622])).

tff(c_746,plain,(
    k3_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_725,c_42])).

tff(c_763,plain,(
    k3_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_746])).

tff(c_904,plain,(
    ! [A_169,B_170,C_171] :
      ( m1_subset_1(k3_relset_1(A_169,B_170,C_171),k1_zfmisc_1(k2_zfmisc_1(B_170,A_169)))
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_928,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_763,c_904])).

tff(c_945,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_725,c_928])).

tff(c_974,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_945,c_16])).

tff(c_983,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_974])).

tff(c_980,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_945,c_30])).

tff(c_986,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_980,c_50])).

tff(c_992,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_983,c_986])).

tff(c_1090,plain,(
    ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_992])).

tff(c_1092,plain,(
    ! [C_176,A_177,B_178] :
      ( v1_partfun1(C_176,A_177)
      | ~ v1_funct_2(C_176,A_177,B_178)
      | ~ v1_funct_1(C_176)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_177,B_178))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_241,c_44])).

tff(c_1095,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_945,c_1092])).

tff(c_1114,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_1090,c_1095])).

tff(c_1120,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1114])).

tff(c_623,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_131])).

tff(c_726,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_717,c_623])).

tff(c_722,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_717,c_716])).

tff(c_1186,plain,(
    ! [C_179,A_180,B_181] :
      ( v1_funct_1(k2_funct_1(C_179))
      | k2_relset_1(A_180,B_181,C_179) != B_181
      | ~ v2_funct_1(C_179)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181)))
      | ~ v1_funct_2(C_179,A_180,B_181)
      | ~ v1_funct_1(C_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_1202,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_725,c_1186])).

tff(c_1217,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_726,c_66,c_722,c_1202])).

tff(c_1219,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1120,c_1217])).

tff(c_1220,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1114])).

tff(c_1470,plain,(
    ! [C_205,B_206,A_207] :
      ( v1_funct_2(k2_funct_1(C_205),B_206,A_207)
      | k2_relset_1(A_207,B_206,C_205) != B_206
      | ~ v2_funct_1(C_205)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_207,B_206)))
      | ~ v1_funct_2(C_205,A_207,B_206)
      | ~ v1_funct_1(C_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_1486,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_725,c_1470])).

tff(c_1501,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_726,c_66,c_722,c_1486])).

tff(c_1503,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1220,c_1501])).

tff(c_1504,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_992])).

tff(c_978,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_945,c_38])).

tff(c_1506,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1504,c_978])).

tff(c_2007,plain,(
    ! [A_274,B_275,C_276] :
      ( k2_tops_2(A_274,B_275,C_276) = k2_funct_1(C_276)
      | ~ v2_funct_1(C_276)
      | k2_relset_1(A_274,B_275,C_276) != B_275
      | ~ m1_subset_1(C_276,k1_zfmisc_1(k2_zfmisc_1(A_274,B_275)))
      | ~ v1_funct_2(C_276,A_274,B_275)
      | ~ v1_funct_1(C_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_2023,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_725,c_2007])).

tff(c_2039,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_726,c_722,c_66,c_2023])).

tff(c_703,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_616,c_188])).

tff(c_723,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_717,c_717,c_717,c_703])).

tff(c_2040,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2039,c_723])).

tff(c_2043,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1506,c_2040])).

tff(c_2044,plain,(
    ! [C_88] :
      ( v1_xboole_0(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(splitRight,[status(thm)],[c_238])).

tff(c_3838,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_3781,c_2044])).

tff(c_3847,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3838,c_2])).

tff(c_3860,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3847,c_3753])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_169,plain,(
    ! [C_73,A_4] :
      ( v4_relat_1(C_73,A_4)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_163])).

tff(c_3875,plain,(
    ! [A_440] : v4_relat_1('#skF_3',A_440) ),
    inference(resolution,[status(thm)],[c_3781,c_169])).

tff(c_3885,plain,(
    ! [A_440] :
      ( k7_relat_1('#skF_3',A_440) = '#skF_3'
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3875,c_22])).

tff(c_3976,plain,(
    ! [A_450] : k7_relat_1('#skF_3',A_450) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_3885])).

tff(c_3981,plain,(
    ! [A_450] :
      ( k9_relat_1('#skF_3',A_450) = k2_relat_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3976,c_20])).

tff(c_3986,plain,(
    ! [A_450] : k9_relat_1('#skF_3',A_450) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_3981])).

tff(c_3854,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3847,c_3781])).

tff(c_3868,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3847,c_3847,c_14])).

tff(c_3865,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3847,c_3847,c_12])).

tff(c_3812,plain,(
    ! [A_437,B_438,C_439] :
      ( k3_relset_1(A_437,B_438,C_439) = k4_relat_1(C_439)
      | ~ m1_subset_1(C_439,k1_zfmisc_1(k2_zfmisc_1(A_437,B_438))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_3818,plain,(
    ! [B_5,C_439] :
      ( k3_relset_1(k1_xboole_0,B_5,C_439) = k4_relat_1(C_439)
      | ~ m1_subset_1(C_439,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_3812])).

tff(c_4226,plain,(
    ! [B_474,C_475] :
      ( k3_relset_1('#skF_3',B_474,C_475) = k4_relat_1(C_475)
      | ~ m1_subset_1(C_475,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3847,c_3847,c_3818])).

tff(c_4231,plain,(
    ! [B_474] : k3_relset_1('#skF_3',B_474,'#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3854,c_4226])).

tff(c_4256,plain,(
    ! [B_478] : k3_relset_1('#skF_3',B_478,'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_4231])).

tff(c_36,plain,(
    ! [A_29,B_30,C_31] :
      ( m1_subset_1(k3_relset_1(A_29,B_30,C_31),k1_zfmisc_1(k2_zfmisc_1(B_30,A_29)))
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_4261,plain,(
    ! [B_478] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(B_478,'#skF_3')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_478))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4256,c_36])).

tff(c_4266,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3854,c_3868,c_3865,c_4261])).

tff(c_3861,plain,(
    ! [C_88] :
      ( v1_xboole_0(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3847,c_2044])).

tff(c_4286,plain,(
    v1_xboole_0(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4266,c_3861])).

tff(c_3866,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3847,c_2])).

tff(c_4293,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4286,c_3866])).

tff(c_26,plain,(
    ! [A_16,B_18] :
      ( k9_relat_1(k2_funct_1(A_16),k9_relat_1(A_16,B_18)) = B_18
      | ~ r1_tarski(B_18,k1_relat_1(A_16))
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_4308,plain,(
    ! [B_18] :
      ( k9_relat_1('#skF_3',k9_relat_1('#skF_3',B_18)) = B_18
      | ~ r1_tarski(B_18,k1_relat_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4293,c_26])).

tff(c_4348,plain,(
    ! [B_484] :
      ( k2_relat_1('#skF_3') = B_484
      | ~ r1_tarski(B_484,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_74,c_66,c_3860,c_3986,c_3986,c_4308])).

tff(c_4353,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_8,c_4348])).

tff(c_3945,plain,(
    ! [B_446] : k2_zfmisc_1('#skF_3',B_446) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3847,c_3847,c_14])).

tff(c_4461,plain,(
    ! [B_499,C_500] :
      ( k2_relset_1('#skF_3',B_499,C_500) = k2_relat_1(C_500)
      | ~ m1_subset_1(C_500,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3945,c_40])).

tff(c_4466,plain,(
    ! [B_499] : k2_relset_1('#skF_3',B_499,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3854,c_4461])).

tff(c_4470,plain,(
    ! [B_499] : k2_relset_1('#skF_3',B_499,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4353,c_4466])).

tff(c_3848,plain,(
    k2_relset_1(k1_xboole_0,k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3753,c_2437])).

tff(c_3853,plain,(
    k2_relset_1('#skF_3',k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3847,c_3848])).

tff(c_4471,plain,(
    k2_struct_0('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4470,c_3853])).

tff(c_4495,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4471,c_240])).

tff(c_4500,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3838,c_4495])).

tff(c_4502,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_4522,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_4502,c_60])).

tff(c_4525,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_4522])).

tff(c_4527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4525])).

tff(c_4528,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_6778,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6776,c_6776,c_6776,c_4528])).

tff(c_6965,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6871,c_6871,c_6778])).

tff(c_7935,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7934,c_6965])).

tff(c_7939,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7230,c_7935])).

tff(c_7941,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_4584])).

tff(c_7960,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_7941,c_60])).

tff(c_7963,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_7960])).

tff(c_7965,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_7963])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:52:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.84/2.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.32/2.71  
% 8.32/2.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.32/2.72  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k3_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k4_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 8.32/2.72  
% 8.32/2.72  %Foreground sorts:
% 8.32/2.72  
% 8.32/2.72  
% 8.32/2.72  %Background operators:
% 8.32/2.72  
% 8.32/2.72  
% 8.32/2.72  %Foreground operators:
% 8.32/2.72  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.32/2.72  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.32/2.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.32/2.72  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.32/2.72  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.32/2.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.32/2.72  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.32/2.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.32/2.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.32/2.72  tff(k3_relset_1, type, k3_relset_1: ($i * $i * $i) > $i).
% 8.32/2.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.32/2.72  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 8.32/2.72  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.32/2.72  tff('#skF_2', type, '#skF_2': $i).
% 8.32/2.72  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.32/2.72  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 8.32/2.72  tff('#skF_3', type, '#skF_3': $i).
% 8.32/2.72  tff('#skF_1', type, '#skF_1': $i).
% 8.32/2.72  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.32/2.72  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.32/2.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.32/2.72  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 8.32/2.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.32/2.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.32/2.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.32/2.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.32/2.72  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.32/2.72  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.32/2.72  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 8.32/2.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.32/2.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.32/2.72  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 8.32/2.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.32/2.72  
% 8.42/2.75  tff(f_198, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_2)).
% 8.42/2.75  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.42/2.75  tff(f_154, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 8.42/2.75  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.42/2.75  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.42/2.75  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.42/2.75  tff(f_92, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 8.42/2.75  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.42/2.75  tff(f_134, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 8.42/2.75  tff(f_126, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 8.42/2.75  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 8.42/2.75  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k3_relset_1(A, B, C) = k4_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_relset_1)).
% 8.42/2.75  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k3_relset_1(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_relset_1)).
% 8.42/2.75  tff(f_60, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 8.42/2.75  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 8.42/2.75  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t177_funct_1)).
% 8.42/2.75  tff(f_174, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 8.42/2.75  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.42/2.75  tff(f_150, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 8.42/2.75  tff(f_162, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 8.42/2.75  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.42/2.75  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 8.42/2.75  tff(c_78, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_198])).
% 8.42/2.75  tff(c_76, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_198])).
% 8.42/2.75  tff(c_18, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.42/2.75  tff(c_80, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_198])).
% 8.42/2.75  tff(c_112, plain, (![A_65]: (u1_struct_0(A_65)=k2_struct_0(A_65) | ~l1_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_154])).
% 8.42/2.75  tff(c_120, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_80, c_112])).
% 8.42/2.75  tff(c_119, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_76, c_112])).
% 8.42/2.75  tff(c_70, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_198])).
% 8.42/2.75  tff(c_132, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_119, c_70])).
% 8.42/2.75  tff(c_156, plain, (![B_71, A_72]: (v1_relat_1(B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(A_72)) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.42/2.75  tff(c_159, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_132, c_156])).
% 8.42/2.75  tff(c_162, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_159])).
% 8.42/2.75  tff(c_74, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_198])).
% 8.42/2.75  tff(c_66, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_198])).
% 8.42/2.75  tff(c_8, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.42/2.75  tff(c_6389, plain, (![A_683, B_684, C_685]: (k2_relset_1(A_683, B_684, C_685)=k2_relat_1(C_685) | ~m1_subset_1(C_685, k1_zfmisc_1(k2_zfmisc_1(A_683, B_684))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.42/2.75  tff(c_6399, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_132, c_6389])).
% 8.42/2.75  tff(c_68, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_198])).
% 8.42/2.75  tff(c_140, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_119, c_68])).
% 8.42/2.75  tff(c_6400, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6399, c_140])).
% 8.42/2.75  tff(c_4574, plain, (![C_508, B_509, A_510]: (v1_xboole_0(C_508) | ~m1_subset_1(C_508, k1_zfmisc_1(k2_zfmisc_1(B_509, A_510))) | ~v1_xboole_0(A_510))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.42/2.75  tff(c_4584, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_132, c_4574])).
% 8.42/2.75  tff(c_4585, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_4584])).
% 8.42/2.75  tff(c_6407, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6400, c_4585])).
% 8.42/2.75  tff(c_163, plain, (![C_73, A_74, B_75]: (v4_relat_1(C_73, A_74) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.42/2.75  tff(c_173, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_132, c_163])).
% 8.42/2.75  tff(c_6364, plain, (![B_676, A_677]: (k1_relat_1(B_676)=A_677 | ~v1_partfun1(B_676, A_677) | ~v4_relat_1(B_676, A_677) | ~v1_relat_1(B_676))), inference(cnfTransformation, [status(thm)], [f_134])).
% 8.42/2.75  tff(c_6367, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_173, c_6364])).
% 8.42/2.75  tff(c_6370, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_6367])).
% 8.42/2.75  tff(c_6371, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_6370])).
% 8.42/2.75  tff(c_72, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_198])).
% 8.42/2.75  tff(c_121, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_72])).
% 8.42/2.75  tff(c_131, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_121])).
% 8.42/2.75  tff(c_6412, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6400, c_131])).
% 8.42/2.75  tff(c_6411, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_6400, c_132])).
% 8.42/2.75  tff(c_6746, plain, (![C_724, A_725, B_726]: (v1_partfun1(C_724, A_725) | ~v1_funct_2(C_724, A_725, B_726) | ~v1_funct_1(C_724) | ~m1_subset_1(C_724, k1_zfmisc_1(k2_zfmisc_1(A_725, B_726))) | v1_xboole_0(B_726))), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.42/2.75  tff(c_6759, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_6411, c_6746])).
% 8.42/2.75  tff(c_6773, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_6412, c_6759])).
% 8.42/2.75  tff(c_6775, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6407, c_6371, c_6773])).
% 8.42/2.75  tff(c_6776, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_6370])).
% 8.42/2.75  tff(c_6784, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_6776, c_132])).
% 8.42/2.75  tff(c_40, plain, (![A_35, B_36, C_37]: (k2_relset_1(A_35, B_36, C_37)=k2_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.42/2.75  tff(c_6858, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6784, c_40])).
% 8.42/2.75  tff(c_6783, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6776, c_140])).
% 8.42/2.75  tff(c_6871, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6858, c_6783])).
% 8.42/2.75  tff(c_6877, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_6871, c_6784])).
% 8.42/2.75  tff(c_4563, plain, (![A_507]: (k4_relat_1(A_507)=k2_funct_1(A_507) | ~v2_funct_1(A_507) | ~v1_funct_1(A_507) | ~v1_relat_1(A_507))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.42/2.75  tff(c_4566, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_4563])).
% 8.42/2.75  tff(c_4569, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_74, c_4566])).
% 8.42/2.75  tff(c_42, plain, (![A_38, B_39, C_40]: (k3_relset_1(A_38, B_39, C_40)=k4_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.42/2.75  tff(c_6905, plain, (k3_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6877, c_42])).
% 8.42/2.75  tff(c_6922, plain, (k3_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4569, c_6905])).
% 8.42/2.75  tff(c_7064, plain, (![A_753, B_754, C_755]: (m1_subset_1(k3_relset_1(A_753, B_754, C_755), k1_zfmisc_1(k2_zfmisc_1(B_754, A_753))) | ~m1_subset_1(C_755, k1_zfmisc_1(k2_zfmisc_1(A_753, B_754))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.42/2.75  tff(c_7088, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_6922, c_7064])).
% 8.42/2.75  tff(c_7105, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_6877, c_7088])).
% 8.42/2.75  tff(c_16, plain, (![B_8, A_6]: (v1_relat_1(B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_6)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.42/2.75  tff(c_7128, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_7105, c_16])).
% 8.42/2.75  tff(c_7137, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_7128])).
% 8.42/2.75  tff(c_30, plain, (![C_21, A_19, B_20]: (v4_relat_1(C_21, A_19) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.42/2.75  tff(c_7134, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_7105, c_30])).
% 8.42/2.75  tff(c_22, plain, (![B_14, A_13]: (k7_relat_1(B_14, A_13)=B_14 | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.42/2.75  tff(c_7143, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_7134, c_22])).
% 8.42/2.75  tff(c_7149, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7137, c_7143])).
% 8.42/2.75  tff(c_20, plain, (![B_12, A_11]: (k2_relat_1(k7_relat_1(B_12, A_11))=k9_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.42/2.75  tff(c_7153, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_7149, c_20])).
% 8.42/2.75  tff(c_7157, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7137, c_7153])).
% 8.42/2.75  tff(c_4543, plain, (![B_505, A_506]: (k7_relat_1(B_505, A_506)=B_505 | ~v4_relat_1(B_505, A_506) | ~v1_relat_1(B_505))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.42/2.75  tff(c_4546, plain, (k7_relat_1('#skF_3', k2_struct_0('#skF_1'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_173, c_4543])).
% 8.42/2.75  tff(c_4549, plain, (k7_relat_1('#skF_3', k2_struct_0('#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_162, c_4546])).
% 8.42/2.75  tff(c_4553, plain, (k9_relat_1('#skF_3', k2_struct_0('#skF_1'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4549, c_20])).
% 8.42/2.75  tff(c_4557, plain, (k9_relat_1('#skF_3', k2_struct_0('#skF_1'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_4553])).
% 8.42/2.75  tff(c_6779, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6776, c_4557])).
% 8.42/2.75  tff(c_7187, plain, (![A_762, B_763]: (k9_relat_1(k2_funct_1(A_762), k9_relat_1(A_762, B_763))=B_763 | ~r1_tarski(B_763, k1_relat_1(A_762)) | ~v2_funct_1(A_762) | ~v1_funct_1(A_762) | ~v1_relat_1(A_762))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.42/2.75  tff(c_7205, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6779, c_7187])).
% 8.42/2.75  tff(c_7211, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_74, c_66, c_8, c_7157, c_7205])).
% 8.42/2.75  tff(c_7131, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_7105, c_40])).
% 8.42/2.75  tff(c_7230, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7211, c_7131])).
% 8.42/2.75  tff(c_6785, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6776, c_131])).
% 8.42/2.75  tff(c_6878, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6871, c_6785])).
% 8.42/2.75  tff(c_6876, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6871, c_6858])).
% 8.42/2.75  tff(c_7903, plain, (![A_836, B_837, C_838]: (k2_tops_2(A_836, B_837, C_838)=k2_funct_1(C_838) | ~v2_funct_1(C_838) | k2_relset_1(A_836, B_837, C_838)!=B_837 | ~m1_subset_1(C_838, k1_zfmisc_1(k2_zfmisc_1(A_836, B_837))) | ~v1_funct_2(C_838, A_836, B_837) | ~v1_funct_1(C_838))), inference(cnfTransformation, [status(thm)], [f_174])).
% 8.42/2.75  tff(c_7919, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_6877, c_7903])).
% 8.42/2.75  tff(c_7934, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_6878, c_6876, c_66, c_7919])).
% 8.42/2.75  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.42/2.75  tff(c_2087, plain, (![A_289, B_290, C_291]: (k2_relset_1(A_289, B_290, C_291)=k2_relat_1(C_291) | ~m1_subset_1(C_291, k1_zfmisc_1(k2_zfmisc_1(A_289, B_290))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.42/2.75  tff(c_2097, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_132, c_2087])).
% 8.42/2.75  tff(c_2098, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2097, c_140])).
% 8.42/2.75  tff(c_229, plain, (![C_88, B_89, A_90]: (v1_xboole_0(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(B_89, A_90))) | ~v1_xboole_0(A_90))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.42/2.75  tff(c_239, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_132, c_229])).
% 8.42/2.75  tff(c_240, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_239])).
% 8.42/2.75  tff(c_2107, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2098, c_240])).
% 8.42/2.75  tff(c_2047, plain, (![B_279, A_280]: (k1_relat_1(B_279)=A_280 | ~v1_partfun1(B_279, A_280) | ~v4_relat_1(B_279, A_280) | ~v1_relat_1(B_279))), inference(cnfTransformation, [status(thm)], [f_134])).
% 8.42/2.75  tff(c_2050, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_173, c_2047])).
% 8.42/2.75  tff(c_2053, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_2050])).
% 8.42/2.75  tff(c_2054, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_2053])).
% 8.42/2.75  tff(c_2110, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2098, c_131])).
% 8.42/2.75  tff(c_2109, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_2098, c_132])).
% 8.42/2.75  tff(c_2402, plain, (![C_308, A_309, B_310]: (v1_partfun1(C_308, A_309) | ~v1_funct_2(C_308, A_309, B_310) | ~v1_funct_1(C_308) | ~m1_subset_1(C_308, k1_zfmisc_1(k2_zfmisc_1(A_309, B_310))) | v1_xboole_0(B_310))), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.42/2.75  tff(c_2411, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_2109, c_2402])).
% 8.42/2.75  tff(c_2428, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2110, c_2411])).
% 8.42/2.75  tff(c_2430, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2107, c_2054, c_2428])).
% 8.42/2.75  tff(c_2431, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_2053])).
% 8.42/2.75  tff(c_2438, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_2431, c_132])).
% 8.42/2.75  tff(c_2547, plain, (![A_321, B_322, C_323]: (k2_relset_1(A_321, B_322, C_323)=k2_relat_1(C_323) | ~m1_subset_1(C_323, k1_zfmisc_1(k2_zfmisc_1(A_321, B_322))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.42/2.75  tff(c_2557, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2438, c_2547])).
% 8.42/2.75  tff(c_2437, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2431, c_140])).
% 8.42/2.75  tff(c_2558, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2557, c_2437])).
% 8.42/2.75  tff(c_2566, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_2558, c_2438])).
% 8.42/2.75  tff(c_214, plain, (![A_87]: (k4_relat_1(A_87)=k2_funct_1(A_87) | ~v2_funct_1(A_87) | ~v1_funct_1(A_87) | ~v1_relat_1(A_87))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.42/2.75  tff(c_217, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_214])).
% 8.42/2.75  tff(c_220, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_74, c_217])).
% 8.42/2.75  tff(c_2531, plain, (![A_318, B_319, C_320]: (k3_relset_1(A_318, B_319, C_320)=k4_relat_1(C_320) | ~m1_subset_1(C_320, k1_zfmisc_1(k2_zfmisc_1(A_318, B_319))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.42/2.75  tff(c_2534, plain, (k3_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2438, c_2531])).
% 8.42/2.75  tff(c_2542, plain, (k3_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_220, c_2534])).
% 8.42/2.75  tff(c_2564, plain, (k3_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2558, c_2542])).
% 8.42/2.75  tff(c_2716, plain, (![A_331, B_332, C_333]: (m1_subset_1(k3_relset_1(A_331, B_332, C_333), k1_zfmisc_1(k2_zfmisc_1(B_332, A_331))) | ~m1_subset_1(C_333, k1_zfmisc_1(k2_zfmisc_1(A_331, B_332))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.42/2.75  tff(c_2740, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_2564, c_2716])).
% 8.42/2.75  tff(c_2757, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_2566, c_2740])).
% 8.42/2.75  tff(c_2780, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_2757, c_16])).
% 8.42/2.75  tff(c_2789, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2780])).
% 8.42/2.75  tff(c_2786, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_2757, c_30])).
% 8.42/2.75  tff(c_50, plain, (![B_46, A_45]: (k1_relat_1(B_46)=A_45 | ~v1_partfun1(B_46, A_45) | ~v4_relat_1(B_46, A_45) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_134])).
% 8.42/2.75  tff(c_2792, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2786, c_50])).
% 8.42/2.75  tff(c_2798, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2789, c_2792])).
% 8.42/2.75  tff(c_2914, plain, (~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2798])).
% 8.42/2.75  tff(c_2439, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2431, c_131])).
% 8.42/2.75  tff(c_2567, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2558, c_2439])).
% 8.42/2.75  tff(c_2563, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2558, c_2557])).
% 8.42/2.75  tff(c_3011, plain, (![C_351, A_352, B_353]: (v1_funct_1(k2_funct_1(C_351)) | k2_relset_1(A_352, B_353, C_351)!=B_353 | ~v2_funct_1(C_351) | ~m1_subset_1(C_351, k1_zfmisc_1(k2_zfmisc_1(A_352, B_353))) | ~v1_funct_2(C_351, A_352, B_353) | ~v1_funct_1(C_351))), inference(cnfTransformation, [status(thm)], [f_150])).
% 8.42/2.75  tff(c_3027, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2566, c_3011])).
% 8.42/2.75  tff(c_3042, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2567, c_66, c_2563, c_3027])).
% 8.42/2.75  tff(c_60, plain, (![A_51]: (~v1_xboole_0(k2_struct_0(A_51)) | ~l1_struct_0(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_162])).
% 8.42/2.75  tff(c_2444, plain, (~v1_xboole_0(k1_relat_1('#skF_3')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2431, c_60])).
% 8.42/2.75  tff(c_2448, plain, (~v1_xboole_0(k1_relat_1('#skF_3')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2444])).
% 8.42/2.75  tff(c_2484, plain, (~v1_xboole_0(k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2448])).
% 8.42/2.75  tff(c_2915, plain, (![C_348, A_349, B_350]: (v1_partfun1(C_348, A_349) | ~v1_funct_2(C_348, A_349, B_350) | ~v1_funct_1(C_348) | ~m1_subset_1(C_348, k1_zfmisc_1(k2_zfmisc_1(A_349, B_350))) | v1_xboole_0(B_350))), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.42/2.75  tff(c_2918, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | v1_xboole_0(k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_2757, c_2915])).
% 8.42/2.75  tff(c_2937, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_2484, c_2918])).
% 8.42/2.75  tff(c_3080, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3042, c_2937])).
% 8.42/2.75  tff(c_3081, plain, (~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_2914, c_3080])).
% 8.42/2.75  tff(c_3155, plain, (![C_368, B_369, A_370]: (v1_funct_2(k2_funct_1(C_368), B_369, A_370) | k2_relset_1(A_370, B_369, C_368)!=B_369 | ~v2_funct_1(C_368) | ~m1_subset_1(C_368, k1_zfmisc_1(k2_zfmisc_1(A_370, B_369))) | ~v1_funct_2(C_368, A_370, B_369) | ~v1_funct_1(C_368))), inference(cnfTransformation, [status(thm)], [f_150])).
% 8.42/2.75  tff(c_3171, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2566, c_3155])).
% 8.42/2.75  tff(c_3186, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2567, c_66, c_2563, c_3171])).
% 8.42/2.75  tff(c_3188, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3081, c_3186])).
% 8.42/2.75  tff(c_3189, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_2798])).
% 8.42/2.75  tff(c_38, plain, (![A_32, B_33, C_34]: (k1_relset_1(A_32, B_33, C_34)=k1_relat_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.42/2.75  tff(c_2783, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2757, c_38])).
% 8.42/2.75  tff(c_3191, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3189, c_2783])).
% 8.42/2.75  tff(c_3711, plain, (![A_434, B_435, C_436]: (k2_tops_2(A_434, B_435, C_436)=k2_funct_1(C_436) | ~v2_funct_1(C_436) | k2_relset_1(A_434, B_435, C_436)!=B_435 | ~m1_subset_1(C_436, k1_zfmisc_1(k2_zfmisc_1(A_434, B_435))) | ~v1_funct_2(C_436, A_434, B_435) | ~v1_funct_1(C_436))), inference(cnfTransformation, [status(thm)], [f_174])).
% 8.42/2.75  tff(c_3727, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2566, c_3711])).
% 8.42/2.75  tff(c_3743, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2567, c_2563, c_66, c_3727])).
% 8.42/2.75  tff(c_64, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_198])).
% 8.42/2.75  tff(c_187, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_120, c_119, c_119, c_120, c_120, c_119, c_119, c_64])).
% 8.42/2.75  tff(c_188, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_187])).
% 8.42/2.75  tff(c_2433, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2431, c_2431, c_188])).
% 8.42/2.75  tff(c_2700, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2558, c_2558, c_2558, c_2433])).
% 8.42/2.75  tff(c_3744, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3743, c_2700])).
% 8.42/2.75  tff(c_3747, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3191, c_3744])).
% 8.42/2.75  tff(c_3749, plain, (v1_xboole_0(k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2448])).
% 8.42/2.75  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.42/2.75  tff(c_3753, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_3749, c_2])).
% 8.42/2.75  tff(c_3774, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_3753, c_2438])).
% 8.42/2.75  tff(c_3781, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_3774])).
% 8.42/2.75  tff(c_246, plain, (![B_93, A_94]: (k1_relat_1(B_93)=A_94 | ~v1_partfun1(B_93, A_94) | ~v4_relat_1(B_93, A_94) | ~v1_relat_1(B_93))), inference(cnfTransformation, [status(thm)], [f_134])).
% 8.42/2.75  tff(c_249, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_173, c_246])).
% 8.42/2.75  tff(c_252, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_249])).
% 8.42/2.75  tff(c_253, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_252])).
% 8.42/2.75  tff(c_271, plain, (![A_102, B_103, C_104]: (k2_relset_1(A_102, B_103, C_104)=k2_relat_1(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.42/2.75  tff(c_281, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_132, c_271])).
% 8.42/2.75  tff(c_282, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_281, c_140])).
% 8.42/2.75  tff(c_291, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_282, c_131])).
% 8.42/2.75  tff(c_290, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_282, c_132])).
% 8.42/2.75  tff(c_238, plain, (![C_88, B_5]: (v1_xboole_0(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(B_5))), inference(superposition, [status(thm), theory('equality')], [c_14, c_229])).
% 8.42/2.75  tff(c_241, plain, (![B_5]: (~v1_xboole_0(B_5))), inference(splitLeft, [status(thm)], [c_238])).
% 8.42/2.75  tff(c_44, plain, (![C_44, A_41, B_42]: (v1_partfun1(C_44, A_41) | ~v1_funct_2(C_44, A_41, B_42) | ~v1_funct_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))) | v1_xboole_0(B_42))), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.42/2.75  tff(c_588, plain, (![C_133, A_134, B_135]: (v1_partfun1(C_133, A_134) | ~v1_funct_2(C_133, A_134, B_135) | ~v1_funct_1(C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))))), inference(negUnitSimplification, [status(thm)], [c_241, c_44])).
% 8.42/2.75  tff(c_601, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_290, c_588])).
% 8.42/2.75  tff(c_613, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_291, c_601])).
% 8.42/2.75  tff(c_615, plain, $false, inference(negUnitSimplification, [status(thm)], [c_253, c_613])).
% 8.42/2.75  tff(c_616, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_252])).
% 8.42/2.75  tff(c_622, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_616, c_132])).
% 8.42/2.75  tff(c_706, plain, (![A_143, B_144, C_145]: (k2_relset_1(A_143, B_144, C_145)=k2_relat_1(C_145) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.42/2.75  tff(c_716, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_622, c_706])).
% 8.42/2.75  tff(c_621, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_616, c_140])).
% 8.42/2.75  tff(c_717, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_716, c_621])).
% 8.42/2.75  tff(c_725, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_717, c_622])).
% 8.42/2.75  tff(c_746, plain, (k3_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_725, c_42])).
% 8.42/2.75  tff(c_763, plain, (k3_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_220, c_746])).
% 8.42/2.75  tff(c_904, plain, (![A_169, B_170, C_171]: (m1_subset_1(k3_relset_1(A_169, B_170, C_171), k1_zfmisc_1(k2_zfmisc_1(B_170, A_169))) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.42/2.75  tff(c_928, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_763, c_904])).
% 8.42/2.75  tff(c_945, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_725, c_928])).
% 8.42/2.75  tff(c_974, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_945, c_16])).
% 8.42/2.75  tff(c_983, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_974])).
% 8.42/2.75  tff(c_980, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_945, c_30])).
% 8.42/2.75  tff(c_986, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_980, c_50])).
% 8.42/2.75  tff(c_992, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_983, c_986])).
% 8.42/2.75  tff(c_1090, plain, (~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_992])).
% 8.42/2.75  tff(c_1092, plain, (![C_176, A_177, B_178]: (v1_partfun1(C_176, A_177) | ~v1_funct_2(C_176, A_177, B_178) | ~v1_funct_1(C_176) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(A_177, B_178))))), inference(negUnitSimplification, [status(thm)], [c_241, c_44])).
% 8.42/2.75  tff(c_1095, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_945, c_1092])).
% 8.42/2.75  tff(c_1114, plain, (~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1090, c_1095])).
% 8.42/2.75  tff(c_1120, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1114])).
% 8.42/2.75  tff(c_623, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_616, c_131])).
% 8.42/2.75  tff(c_726, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_717, c_623])).
% 8.42/2.75  tff(c_722, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_717, c_716])).
% 8.42/2.75  tff(c_1186, plain, (![C_179, A_180, B_181]: (v1_funct_1(k2_funct_1(C_179)) | k2_relset_1(A_180, B_181, C_179)!=B_181 | ~v2_funct_1(C_179) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))) | ~v1_funct_2(C_179, A_180, B_181) | ~v1_funct_1(C_179))), inference(cnfTransformation, [status(thm)], [f_150])).
% 8.42/2.75  tff(c_1202, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_725, c_1186])).
% 8.42/2.75  tff(c_1217, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_726, c_66, c_722, c_1202])).
% 8.42/2.75  tff(c_1219, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1120, c_1217])).
% 8.42/2.75  tff(c_1220, plain, (~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1114])).
% 8.42/2.75  tff(c_1470, plain, (![C_205, B_206, A_207]: (v1_funct_2(k2_funct_1(C_205), B_206, A_207) | k2_relset_1(A_207, B_206, C_205)!=B_206 | ~v2_funct_1(C_205) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(A_207, B_206))) | ~v1_funct_2(C_205, A_207, B_206) | ~v1_funct_1(C_205))), inference(cnfTransformation, [status(thm)], [f_150])).
% 8.42/2.75  tff(c_1486, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_725, c_1470])).
% 8.42/2.75  tff(c_1501, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_726, c_66, c_722, c_1486])).
% 8.42/2.75  tff(c_1503, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1220, c_1501])).
% 8.42/2.75  tff(c_1504, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_992])).
% 8.42/2.75  tff(c_978, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_945, c_38])).
% 8.42/2.75  tff(c_1506, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1504, c_978])).
% 8.42/2.75  tff(c_2007, plain, (![A_274, B_275, C_276]: (k2_tops_2(A_274, B_275, C_276)=k2_funct_1(C_276) | ~v2_funct_1(C_276) | k2_relset_1(A_274, B_275, C_276)!=B_275 | ~m1_subset_1(C_276, k1_zfmisc_1(k2_zfmisc_1(A_274, B_275))) | ~v1_funct_2(C_276, A_274, B_275) | ~v1_funct_1(C_276))), inference(cnfTransformation, [status(thm)], [f_174])).
% 8.42/2.75  tff(c_2023, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_725, c_2007])).
% 8.42/2.75  tff(c_2039, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_726, c_722, c_66, c_2023])).
% 8.42/2.75  tff(c_703, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_616, c_616, c_188])).
% 8.42/2.75  tff(c_723, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_717, c_717, c_717, c_703])).
% 8.42/2.75  tff(c_2040, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2039, c_723])).
% 8.42/2.75  tff(c_2043, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1506, c_2040])).
% 8.42/2.75  tff(c_2044, plain, (![C_88]: (v1_xboole_0(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_238])).
% 8.42/2.75  tff(c_3838, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_3781, c_2044])).
% 8.42/2.75  tff(c_3847, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3838, c_2])).
% 8.42/2.75  tff(c_3860, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3847, c_3753])).
% 8.42/2.75  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.42/2.75  tff(c_169, plain, (![C_73, A_4]: (v4_relat_1(C_73, A_4) | ~m1_subset_1(C_73, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_163])).
% 8.42/2.75  tff(c_3875, plain, (![A_440]: (v4_relat_1('#skF_3', A_440))), inference(resolution, [status(thm)], [c_3781, c_169])).
% 8.42/2.75  tff(c_3885, plain, (![A_440]: (k7_relat_1('#skF_3', A_440)='#skF_3' | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_3875, c_22])).
% 8.42/2.75  tff(c_3976, plain, (![A_450]: (k7_relat_1('#skF_3', A_450)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_3885])).
% 8.42/2.75  tff(c_3981, plain, (![A_450]: (k9_relat_1('#skF_3', A_450)=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3976, c_20])).
% 8.42/2.75  tff(c_3986, plain, (![A_450]: (k9_relat_1('#skF_3', A_450)=k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_3981])).
% 8.42/2.75  tff(c_3854, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3847, c_3781])).
% 8.42/2.75  tff(c_3868, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3847, c_3847, c_14])).
% 8.42/2.75  tff(c_3865, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3847, c_3847, c_12])).
% 8.42/2.75  tff(c_3812, plain, (![A_437, B_438, C_439]: (k3_relset_1(A_437, B_438, C_439)=k4_relat_1(C_439) | ~m1_subset_1(C_439, k1_zfmisc_1(k2_zfmisc_1(A_437, B_438))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.42/2.75  tff(c_3818, plain, (![B_5, C_439]: (k3_relset_1(k1_xboole_0, B_5, C_439)=k4_relat_1(C_439) | ~m1_subset_1(C_439, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_3812])).
% 8.42/2.75  tff(c_4226, plain, (![B_474, C_475]: (k3_relset_1('#skF_3', B_474, C_475)=k4_relat_1(C_475) | ~m1_subset_1(C_475, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_3847, c_3847, c_3818])).
% 8.42/2.75  tff(c_4231, plain, (![B_474]: (k3_relset_1('#skF_3', B_474, '#skF_3')=k4_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_3854, c_4226])).
% 8.42/2.75  tff(c_4256, plain, (![B_478]: (k3_relset_1('#skF_3', B_478, '#skF_3')=k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_4231])).
% 8.42/2.75  tff(c_36, plain, (![A_29, B_30, C_31]: (m1_subset_1(k3_relset_1(A_29, B_30, C_31), k1_zfmisc_1(k2_zfmisc_1(B_30, A_29))) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.42/2.75  tff(c_4261, plain, (![B_478]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(B_478, '#skF_3'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_478))))), inference(superposition, [status(thm), theory('equality')], [c_4256, c_36])).
% 8.42/2.75  tff(c_4266, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3854, c_3868, c_3865, c_4261])).
% 8.42/2.75  tff(c_3861, plain, (![C_88]: (v1_xboole_0(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_3847, c_2044])).
% 8.42/2.75  tff(c_4286, plain, (v1_xboole_0(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_4266, c_3861])).
% 8.42/2.75  tff(c_3866, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_3847, c_2])).
% 8.42/2.75  tff(c_4293, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_4286, c_3866])).
% 8.42/2.75  tff(c_26, plain, (![A_16, B_18]: (k9_relat_1(k2_funct_1(A_16), k9_relat_1(A_16, B_18))=B_18 | ~r1_tarski(B_18, k1_relat_1(A_16)) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.42/2.75  tff(c_4308, plain, (![B_18]: (k9_relat_1('#skF_3', k9_relat_1('#skF_3', B_18))=B_18 | ~r1_tarski(B_18, k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4293, c_26])).
% 8.42/2.75  tff(c_4348, plain, (![B_484]: (k2_relat_1('#skF_3')=B_484 | ~r1_tarski(B_484, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_74, c_66, c_3860, c_3986, c_3986, c_4308])).
% 8.42/2.75  tff(c_4353, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_8, c_4348])).
% 8.42/2.75  tff(c_3945, plain, (![B_446]: (k2_zfmisc_1('#skF_3', B_446)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3847, c_3847, c_14])).
% 8.42/2.75  tff(c_4461, plain, (![B_499, C_500]: (k2_relset_1('#skF_3', B_499, C_500)=k2_relat_1(C_500) | ~m1_subset_1(C_500, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3945, c_40])).
% 8.42/2.75  tff(c_4466, plain, (![B_499]: (k2_relset_1('#skF_3', B_499, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_3854, c_4461])).
% 8.42/2.75  tff(c_4470, plain, (![B_499]: (k2_relset_1('#skF_3', B_499, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4353, c_4466])).
% 8.42/2.75  tff(c_3848, plain, (k2_relset_1(k1_xboole_0, k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3753, c_2437])).
% 8.42/2.75  tff(c_3853, plain, (k2_relset_1('#skF_3', k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3847, c_3848])).
% 8.42/2.75  tff(c_4471, plain, (k2_struct_0('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4470, c_3853])).
% 8.42/2.75  tff(c_4495, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4471, c_240])).
% 8.42/2.75  tff(c_4500, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3838, c_4495])).
% 8.42/2.75  tff(c_4502, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_239])).
% 8.42/2.75  tff(c_4522, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_4502, c_60])).
% 8.42/2.75  tff(c_4525, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_4522])).
% 8.42/2.75  tff(c_4527, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_4525])).
% 8.42/2.75  tff(c_4528, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_187])).
% 8.42/2.75  tff(c_6778, plain, (k2_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6776, c_6776, c_6776, c_4528])).
% 8.42/2.75  tff(c_6965, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6871, c_6871, c_6778])).
% 8.42/2.75  tff(c_7935, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7934, c_6965])).
% 8.42/2.75  tff(c_7939, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7230, c_7935])).
% 8.42/2.75  tff(c_7941, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_4584])).
% 8.42/2.75  tff(c_7960, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_7941, c_60])).
% 8.42/2.75  tff(c_7963, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_7960])).
% 8.42/2.75  tff(c_7965, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_7963])).
% 8.42/2.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.42/2.75  
% 8.42/2.75  Inference rules
% 8.42/2.75  ----------------------
% 8.42/2.75  #Ref     : 0
% 8.42/2.75  #Sup     : 1879
% 8.42/2.75  #Fact    : 0
% 8.42/2.75  #Define  : 0
% 8.42/2.75  #Split   : 37
% 8.42/2.75  #Chain   : 0
% 8.42/2.75  #Close   : 0
% 8.42/2.75  
% 8.42/2.75  Ordering : KBO
% 8.42/2.75  
% 8.42/2.75  Simplification rules
% 8.42/2.75  ----------------------
% 8.42/2.75  #Subsume      : 106
% 8.42/2.75  #Demod        : 1113
% 8.42/2.75  #Tautology    : 614
% 8.42/2.75  #SimpNegUnit  : 45
% 8.42/2.75  #BackRed      : 175
% 8.42/2.75  
% 8.42/2.75  #Partial instantiations: 0
% 8.42/2.76  #Strategies tried      : 1
% 8.42/2.76  
% 8.42/2.76  Timing (in seconds)
% 8.42/2.76  ----------------------
% 8.42/2.76  Preprocessing        : 0.41
% 8.42/2.76  Parsing              : 0.22
% 8.42/2.76  CNF conversion       : 0.03
% 8.42/2.76  Main loop            : 1.48
% 8.42/2.76  Inferencing          : 0.52
% 8.42/2.76  Reduction            : 0.51
% 8.42/2.76  Demodulation         : 0.36
% 8.42/2.76  BG Simplification    : 0.06
% 8.42/2.76  Subsumption          : 0.24
% 8.42/2.76  Abstraction          : 0.07
% 8.42/2.76  MUC search           : 0.00
% 8.42/2.76  Cooper               : 0.00
% 8.42/2.76  Total                : 1.98
% 8.42/2.76  Index Insertion      : 0.00
% 8.42/2.76  Index Deletion       : 0.00
% 8.42/2.76  Index Matching       : 0.00
% 8.42/2.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
