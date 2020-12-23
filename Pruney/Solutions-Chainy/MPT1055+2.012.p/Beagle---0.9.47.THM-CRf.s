%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:20 EST 2020

% Result     : Theorem 41.34s
% Output     : CNFRefutation 41.34s
% Verified   : 
% Statistics : Number of formulae       :  203 (1283 expanded)
%              Number of leaves         :   54 ( 471 expanded)
%              Depth                    :   17
%              Number of atoms          :  407 (3904 expanded)
%              Number of equality atoms :   55 ( 508 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_251,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(A))
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(B))
                       => ( r1_tarski(k7_relset_1(A,B,C,D),E)
                        <=> r1_tarski(D,k8_relset_1(A,B,C,E)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_2)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_94,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_156,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_152,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_182,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_160,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_214,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).

tff(f_125,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_226,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_168,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_relat_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_135,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_148,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_202,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & ~ v1_xboole_0(C)
              & v1_funct_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_funct_2)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_104,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_96,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_156,plain,(
    ! [A_120,B_121] :
      ( r1_tarski(A_120,B_121)
      | ~ m1_subset_1(A_120,k1_zfmisc_1(B_121)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_171,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_96,c_156])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_44,plain,(
    ! [A_27,B_28] : v1_relat_1(k2_zfmisc_1(A_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_98,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_89827,plain,(
    ! [B_2728,A_2729] :
      ( v1_relat_1(B_2728)
      | ~ m1_subset_1(B_2728,k1_zfmisc_1(A_2729))
      | ~ v1_relat_1(A_2729) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_89833,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_98,c_89827])).

tff(c_89846,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_89833])).

tff(c_102,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_142556,plain,(
    ! [A_4653,B_4654,C_4655,D_4656] :
      ( k7_relset_1(A_4653,B_4654,C_4655,D_4656) = k9_relat_1(C_4655,D_4656)
      | ~ m1_subset_1(C_4655,k1_zfmisc_1(k2_zfmisc_1(A_4653,B_4654))) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_142570,plain,(
    ! [D_4656] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_4656) = k9_relat_1('#skF_3',D_4656) ),
    inference(resolution,[status(thm)],[c_98,c_142556])).

tff(c_141905,plain,(
    ! [A_4597,B_4598,C_4599] :
      ( k2_relset_1(A_4597,B_4598,C_4599) = k2_relat_1(C_4599)
      | ~ m1_subset_1(C_4599,k1_zfmisc_1(k2_zfmisc_1(A_4597,B_4598))) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_141924,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_141905])).

tff(c_142837,plain,(
    ! [A_4673,B_4674,C_4675] :
      ( k7_relset_1(A_4673,B_4674,C_4675,A_4673) = k2_relset_1(A_4673,B_4674,C_4675)
      | ~ m1_subset_1(C_4675,k1_zfmisc_1(k2_zfmisc_1(A_4673,B_4674))) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_142842,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') = k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_142837])).

tff(c_142852,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142570,c_141924,c_142842])).

tff(c_100,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_142405,plain,(
    ! [A_4635,B_4636,C_4637,D_4638] :
      ( k8_relset_1(A_4635,B_4636,C_4637,D_4638) = k10_relat_1(C_4637,D_4638)
      | ~ m1_subset_1(C_4637,k1_zfmisc_1(k2_zfmisc_1(A_4635,B_4636))) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_142419,plain,(
    ! [D_4638] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_4638) = k10_relat_1('#skF_3',D_4638) ),
    inference(resolution,[status(thm)],[c_98,c_142405])).

tff(c_144839,plain,(
    ! [B_4770,A_4771,C_4772] :
      ( k1_xboole_0 = B_4770
      | k8_relset_1(A_4771,B_4770,C_4772,B_4770) = A_4771
      | ~ m1_subset_1(C_4772,k1_zfmisc_1(k2_zfmisc_1(A_4771,B_4770)))
      | ~ v1_funct_2(C_4772,A_4771,B_4770)
      | ~ v1_funct_1(C_4772) ) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_144850,plain,
    ( k1_xboole_0 = '#skF_2'
    | k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_144839])).

tff(c_144864,plain,
    ( k1_xboole_0 = '#skF_2'
    | k10_relat_1('#skF_3','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_142419,c_144850])).

tff(c_144868,plain,(
    k10_relat_1('#skF_3','#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_144864])).

tff(c_54,plain,(
    ! [B_42,A_41] :
      ( r1_tarski(k9_relat_1(B_42,k10_relat_1(B_42,A_41)),A_41)
      | ~ v1_funct_1(B_42)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_144873,plain,
    ( r1_tarski(k9_relat_1('#skF_3','#skF_1'),'#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_144868,c_54])).

tff(c_144877,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89846,c_102,c_142852,c_144873])).

tff(c_90,plain,(
    ! [B_83,A_82] :
      ( v1_funct_2(B_83,k1_relat_1(B_83),A_82)
      | ~ r1_tarski(k2_relat_1(B_83),A_82)
      | ~ v1_funct_1(B_83)
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_143683,plain,(
    ! [C_4706,A_4707,B_4708] :
      ( m1_subset_1(C_4706,k1_zfmisc_1(k2_zfmisc_1(A_4707,B_4708)))
      | ~ r1_tarski(k2_relat_1(C_4706),B_4708)
      | ~ r1_tarski(k1_relat_1(C_4706),A_4707)
      | ~ v1_relat_1(C_4706) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_28,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_170835,plain,(
    ! [C_5577,A_5578,B_5579] :
      ( r1_tarski(C_5577,k2_zfmisc_1(A_5578,B_5579))
      | ~ r1_tarski(k2_relat_1(C_5577),B_5579)
      | ~ r1_tarski(k1_relat_1(C_5577),A_5578)
      | ~ v1_relat_1(C_5577) ) ),
    inference(resolution,[status(thm)],[c_143683,c_28])).

tff(c_170867,plain,(
    ! [A_5578] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_5578,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_5578)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_144877,c_170835])).

tff(c_170928,plain,(
    ! [A_5580] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_5580,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_5580) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89846,c_170867])).

tff(c_171022,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_8,c_170928])).

tff(c_30,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_142418,plain,(
    ! [A_4635,B_4636,A_15,D_4638] :
      ( k8_relset_1(A_4635,B_4636,A_15,D_4638) = k10_relat_1(A_15,D_4638)
      | ~ r1_tarski(A_15,k2_zfmisc_1(A_4635,B_4636)) ) ),
    inference(resolution,[status(thm)],[c_30,c_142405])).

tff(c_171066,plain,(
    ! [D_4638] : k8_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3',D_4638) = k10_relat_1('#skF_3',D_4638) ),
    inference(resolution,[status(thm)],[c_171022,c_142418])).

tff(c_178649,plain,(
    ! [B_5833,A_5834,A_5835] :
      ( k1_xboole_0 = B_5833
      | k8_relset_1(A_5834,B_5833,A_5835,B_5833) = A_5834
      | ~ v1_funct_2(A_5835,A_5834,B_5833)
      | ~ v1_funct_1(A_5835)
      | ~ r1_tarski(A_5835,k2_zfmisc_1(A_5834,B_5833)) ) ),
    inference(resolution,[status(thm)],[c_30,c_144839])).

tff(c_178661,plain,
    ( k1_xboole_0 = '#skF_2'
    | k8_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_171022,c_178649])).

tff(c_178719,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_144868,c_171066,c_178661])).

tff(c_179430,plain,(
    ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_178719])).

tff(c_179440,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_179430])).

tff(c_179444,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89846,c_102,c_144877,c_179440])).

tff(c_179445,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_178719])).

tff(c_179447,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_179445])).

tff(c_48,plain,(
    ! [B_32,A_31] :
      ( r1_tarski(k9_relat_1(B_32,A_31),k9_relat_1(B_32,k1_relat_1(B_32)))
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_142876,plain,
    ( r1_tarski(k2_relat_1('#skF_3'),k9_relat_1('#skF_3',k1_relat_1('#skF_3')))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_142852,c_48])).

tff(c_142889,plain,(
    r1_tarski(k2_relat_1('#skF_3'),k9_relat_1('#skF_3',k1_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89846,c_142876])).

tff(c_140928,plain,(
    ! [B_4502,A_4503] :
      ( r1_tarski(k9_relat_1(B_4502,A_4503),k2_relat_1(B_4502))
      | ~ v1_relat_1(B_4502) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_165870,plain,(
    ! [B_5458,A_5459] :
      ( k9_relat_1(B_5458,A_5459) = k2_relat_1(B_5458)
      | ~ r1_tarski(k2_relat_1(B_5458),k9_relat_1(B_5458,A_5459))
      | ~ v1_relat_1(B_5458) ) ),
    inference(resolution,[status(thm)],[c_140928,c_4])).

tff(c_165884,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_142889,c_165870])).

tff(c_165916,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89846,c_165884])).

tff(c_56,plain,(
    ! [A_43,C_45,B_44] :
      ( r1_tarski(A_43,k10_relat_1(C_45,B_44))
      | ~ r1_tarski(k9_relat_1(C_45,A_43),B_44)
      | ~ r1_tarski(A_43,k1_relat_1(C_45))
      | ~ v1_funct_1(C_45)
      | ~ v1_relat_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_165960,plain,(
    ! [B_44] :
      ( r1_tarski(k1_relat_1('#skF_3'),k10_relat_1('#skF_3',B_44))
      | ~ r1_tarski(k2_relat_1('#skF_3'),B_44)
      | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165916,c_56])).

tff(c_169277,plain,(
    ! [B_5535] :
      ( r1_tarski(k1_relat_1('#skF_3'),k10_relat_1('#skF_3',B_5535))
      | ~ r1_tarski(k2_relat_1('#skF_3'),B_5535) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89846,c_102,c_8,c_165960])).

tff(c_42,plain,(
    ! [B_26,A_25] :
      ( r1_tarski(k2_relat_1(B_26),A_25)
      | ~ v5_relat_1(B_26,A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_16,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_141643,plain,(
    ! [C_4574,B_4575,A_4576] :
      ( v1_xboole_0(C_4574)
      | ~ m1_subset_1(C_4574,k1_zfmisc_1(k2_zfmisc_1(B_4575,A_4576)))
      | ~ v1_xboole_0(A_4576) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_141660,plain,(
    ! [C_4574] :
      ( v1_xboole_0(C_4574)
      | ~ m1_subset_1(C_4574,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_141643])).

tff(c_141667,plain,(
    ! [C_4577] :
      ( v1_xboole_0(C_4577)
      | ~ m1_subset_1(C_4577,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_141660])).

tff(c_141679,plain,(
    ! [A_4578] :
      ( v1_xboole_0(A_4578)
      | ~ r1_tarski(A_4578,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_30,c_141667])).

tff(c_141697,plain,(
    ! [B_26] :
      ( v1_xboole_0(k2_relat_1(B_26))
      | ~ v5_relat_1(B_26,k1_xboole_0)
      | ~ v1_relat_1(B_26) ) ),
    inference(resolution,[status(thm)],[c_42,c_141679])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( r2_hidden(A_13,B_14)
      | v1_xboole_0(B_14)
      | ~ m1_subset_1(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_141479,plain,(
    ! [A_4553,C_4554,B_4555] :
      ( m1_subset_1(A_4553,C_4554)
      | ~ m1_subset_1(B_4555,k1_zfmisc_1(C_4554))
      | ~ r2_hidden(A_4553,B_4555) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_141791,plain,(
    ! [A_4584,B_4585,A_4586] :
      ( m1_subset_1(A_4584,B_4585)
      | ~ r2_hidden(A_4584,A_4586)
      | ~ r1_tarski(A_4586,B_4585) ) ),
    inference(resolution,[status(thm)],[c_30,c_141479])).

tff(c_141794,plain,(
    ! [A_13,B_4585,B_14] :
      ( m1_subset_1(A_13,B_4585)
      | ~ r1_tarski(B_14,B_4585)
      | v1_xboole_0(B_14)
      | ~ m1_subset_1(A_13,B_14) ) ),
    inference(resolution,[status(thm)],[c_26,c_141791])).

tff(c_144900,plain,(
    ! [A_13] :
      ( m1_subset_1(A_13,'#skF_2')
      | v1_xboole_0(k2_relat_1('#skF_3'))
      | ~ m1_subset_1(A_13,k2_relat_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_144877,c_141794])).

tff(c_145564,plain,(
    v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_144900])).

tff(c_106,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_144072,plain,(
    ! [C_4732,A_4733,B_4734] :
      ( ~ v1_xboole_0(C_4732)
      | ~ v1_funct_2(C_4732,A_4733,B_4734)
      | ~ v1_funct_1(C_4732)
      | ~ m1_subset_1(C_4732,k1_zfmisc_1(k2_zfmisc_1(A_4733,B_4734)))
      | v1_xboole_0(B_4734)
      | v1_xboole_0(A_4733) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_144085,plain,
    ( ~ v1_xboole_0('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_98,c_144072])).

tff(c_144101,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_144085])).

tff(c_144102,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_104,c_144101])).

tff(c_50,plain,(
    ! [C_35,A_33,B_34] :
      ( r1_tarski(k9_relat_1(C_35,A_33),k9_relat_1(C_35,B_34))
      | ~ r1_tarski(A_33,B_34)
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_142867,plain,(
    ! [B_34] :
      ( r1_tarski(k2_relat_1('#skF_3'),k9_relat_1('#skF_3',B_34))
      | ~ r1_tarski('#skF_1',B_34)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142852,c_50])).

tff(c_142883,plain,(
    ! [B_34] :
      ( r1_tarski(k2_relat_1('#skF_3'),k9_relat_1('#skF_3',B_34))
      | ~ r1_tarski('#skF_1',B_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89846,c_142867])).

tff(c_143369,plain,(
    ! [B_4693,A_4694] :
      ( m1_subset_1(B_4693,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_4693),A_4694)))
      | ~ r1_tarski(k2_relat_1(B_4693),A_4694)
      | ~ v1_funct_1(B_4693)
      | ~ v1_relat_1(B_4693) ) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_62,plain,(
    ! [C_52,B_50,A_49] :
      ( v1_xboole_0(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(B_50,A_49)))
      | ~ v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_146446,plain,(
    ! [B_4841,A_4842] :
      ( v1_xboole_0(B_4841)
      | ~ v1_xboole_0(A_4842)
      | ~ r1_tarski(k2_relat_1(B_4841),A_4842)
      | ~ v1_funct_1(B_4841)
      | ~ v1_relat_1(B_4841) ) ),
    inference(resolution,[status(thm)],[c_143369,c_62])).

tff(c_146472,plain,(
    ! [B_34] :
      ( v1_xboole_0('#skF_3')
      | ~ v1_xboole_0(k9_relat_1('#skF_3',B_34))
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski('#skF_1',B_34) ) ),
    inference(resolution,[status(thm)],[c_142883,c_146446])).

tff(c_146516,plain,(
    ! [B_34] :
      ( v1_xboole_0('#skF_3')
      | ~ v1_xboole_0(k9_relat_1('#skF_3',B_34))
      | ~ r1_tarski('#skF_1',B_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89846,c_102,c_146472])).

tff(c_146530,plain,(
    ! [B_4843] :
      ( ~ v1_xboole_0(k9_relat_1('#skF_3',B_4843))
      | ~ r1_tarski('#skF_1',B_4843) ) ),
    inference(negUnitSimplification,[status(thm)],[c_144102,c_146516])).

tff(c_146537,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_142852,c_146530])).

tff(c_146547,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_145564,c_146537])).

tff(c_146549,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_144900])).

tff(c_146552,plain,
    ( ~ v5_relat_1('#skF_3',k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_141697,c_146549])).

tff(c_146555,plain,(
    ~ v5_relat_1('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89846,c_146552])).

tff(c_141722,plain,(
    ! [B_4582,A_4583] :
      ( r1_tarski(k9_relat_1(B_4582,k10_relat_1(B_4582,A_4583)),A_4583)
      | ~ v1_funct_1(B_4582)
      | ~ v1_relat_1(B_4582) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_12,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_141788,plain,(
    ! [B_4582] :
      ( k9_relat_1(B_4582,k10_relat_1(B_4582,k1_xboole_0)) = k1_xboole_0
      | ~ v1_funct_1(B_4582)
      | ~ v1_relat_1(B_4582) ) ),
    inference(resolution,[status(thm)],[c_141722,c_12])).

tff(c_165983,plain,(
    ! [B_34] :
      ( r1_tarski(k2_relat_1('#skF_3'),k9_relat_1('#skF_3',B_34))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_34)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165916,c_50])).

tff(c_167232,plain,(
    ! [B_5489] :
      ( r1_tarski(k2_relat_1('#skF_3'),k9_relat_1('#skF_3',B_5489))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_5489) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89846,c_165983])).

tff(c_40,plain,(
    ! [B_26,A_25] :
      ( v5_relat_1(B_26,A_25)
      | ~ r1_tarski(k2_relat_1(B_26),A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_167270,plain,(
    ! [B_5489] :
      ( v5_relat_1('#skF_3',k9_relat_1('#skF_3',B_5489))
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_5489) ) ),
    inference(resolution,[status(thm)],[c_167232,c_40])).

tff(c_168274,plain,(
    ! [B_5511] :
      ( v5_relat_1('#skF_3',k9_relat_1('#skF_3',B_5511))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_5511) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89846,c_167270])).

tff(c_168292,plain,
    ( v5_relat_1('#skF_3',k1_xboole_0)
    | ~ r1_tarski(k1_relat_1('#skF_3'),k10_relat_1('#skF_3',k1_xboole_0))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_141788,c_168274])).

tff(c_168303,plain,
    ( v5_relat_1('#skF_3',k1_xboole_0)
    | ~ r1_tarski(k1_relat_1('#skF_3'),k10_relat_1('#skF_3',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89846,c_102,c_168292])).

tff(c_168304,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k10_relat_1('#skF_3',k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_146555,c_168303])).

tff(c_169319,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_169277,c_168304])).

tff(c_179497,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179447,c_169319])).

tff(c_179580,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_144877,c_179497])).

tff(c_179581,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_179445])).

tff(c_46,plain,(
    ! [B_30,A_29] :
      ( r1_tarski(k9_relat_1(B_30,A_29),k2_relat_1(B_30))
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_10,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_144928,plain,(
    ! [A_4775] :
      ( r1_tarski(A_4775,'#skF_2')
      | ~ r1_tarski(A_4775,k2_relat_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_144877,c_10])).

tff(c_144955,plain,(
    ! [A_29] :
      ( r1_tarski(k9_relat_1('#skF_3',A_29),'#skF_2')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_144928])).

tff(c_144979,plain,(
    ! [A_4776] : r1_tarski(k9_relat_1('#skF_3',A_4776),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89846,c_144955])).

tff(c_144988,plain,(
    ! [A_4776] :
      ( r1_tarski(A_4776,k10_relat_1('#skF_3','#skF_2'))
      | ~ r1_tarski(A_4776,k1_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_144979,c_56])).

tff(c_145064,plain,(
    ! [A_4779] :
      ( r1_tarski(A_4779,'#skF_1')
      | ~ r1_tarski(A_4779,k1_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89846,c_102,c_144868,c_144988])).

tff(c_145100,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_145064])).

tff(c_145131,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_145100,c_4])).

tff(c_145133,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_145131])).

tff(c_179627,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179581,c_145133])).

tff(c_179642,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_179627])).

tff(c_179643,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_145131])).

tff(c_232,plain,(
    ! [B_133,A_134] :
      ( v1_relat_1(B_133)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(A_134))
      | ~ v1_relat_1(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_238,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_98,c_232])).

tff(c_251,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_238])).

tff(c_1927,plain,(
    ! [A_289,B_290,C_291,D_292] :
      ( k8_relset_1(A_289,B_290,C_291,D_292) = k10_relat_1(C_291,D_292)
      | ~ m1_subset_1(C_291,k1_zfmisc_1(k2_zfmisc_1(A_289,B_290))) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1941,plain,(
    ! [D_292] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_292) = k10_relat_1('#skF_3',D_292) ),
    inference(resolution,[status(thm)],[c_98,c_1927])).

tff(c_114,plain,
    ( r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5')
    | r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_180,plain,(
    r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_1946,plain,(
    r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1941,c_180])).

tff(c_1069,plain,(
    ! [B_224,A_225] :
      ( r1_tarski(k9_relat_1(B_224,k10_relat_1(B_224,A_225)),A_225)
      | ~ v1_funct_1(B_224)
      | ~ v1_relat_1(B_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_47687,plain,(
    ! [A_1643,A_1644,B_1645] :
      ( r1_tarski(A_1643,A_1644)
      | ~ r1_tarski(A_1643,k9_relat_1(B_1645,k10_relat_1(B_1645,A_1644)))
      | ~ v1_funct_1(B_1645)
      | ~ v1_relat_1(B_1645) ) ),
    inference(resolution,[status(thm)],[c_1069,c_10])).

tff(c_89257,plain,(
    ! [C_2719,A_2720,A_2721] :
      ( r1_tarski(k9_relat_1(C_2719,A_2720),A_2721)
      | ~ v1_funct_1(C_2719)
      | ~ r1_tarski(A_2720,k10_relat_1(C_2719,A_2721))
      | ~ v1_relat_1(C_2719) ) ),
    inference(resolution,[status(thm)],[c_50,c_47687])).

tff(c_1797,plain,(
    ! [A_277,B_278,C_279,D_280] :
      ( k7_relset_1(A_277,B_278,C_279,D_280) = k9_relat_1(C_279,D_280)
      | ~ m1_subset_1(C_279,k1_zfmisc_1(k2_zfmisc_1(A_277,B_278))) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_1811,plain,(
    ! [D_280] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_280) = k9_relat_1('#skF_3',D_280) ),
    inference(resolution,[status(thm)],[c_98,c_1797])).

tff(c_108,plain,
    ( ~ r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_219,plain,(
    ~ r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_108])).

tff(c_1821,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1811,c_219])).

tff(c_89617,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_89257,c_1821])).

tff(c_89797,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_1946,c_102,c_89617])).

tff(c_89799,plain,(
    ~ r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_142421,plain,(
    ~ r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142419,c_89799])).

tff(c_89798,plain,(
    r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_142585,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142570,c_89798])).

tff(c_144122,plain,(
    ! [A_4737,C_4738,B_4739] :
      ( r1_tarski(A_4737,k10_relat_1(C_4738,B_4739))
      | ~ r1_tarski(k9_relat_1(C_4738,A_4737),B_4739)
      | ~ r1_tarski(A_4737,k1_relat_1(C_4738))
      | ~ v1_funct_1(C_4738)
      | ~ v1_relat_1(C_4738) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_144150,plain,
    ( r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_142585,c_144122])).

tff(c_144200,plain,
    ( r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89846,c_102,c_144150])).

tff(c_144201,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_142421,c_144200])).

tff(c_179657,plain,(
    ~ r1_tarski('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179643,c_144201])).

tff(c_179665,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_179657])).

tff(c_179666,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_144864])).

tff(c_179725,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179666,c_2])).

tff(c_179728,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_179725])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:46:59 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 41.34/29.95  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 41.34/29.97  
% 41.34/29.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 41.34/29.97  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 41.34/29.97  
% 41.34/29.97  %Foreground sorts:
% 41.34/29.97  
% 41.34/29.97  
% 41.34/29.97  %Background operators:
% 41.34/29.97  
% 41.34/29.97  
% 41.34/29.97  %Foreground operators:
% 41.34/29.97  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 41.34/29.97  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 41.34/29.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 41.34/29.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 41.34/29.97  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 41.34/29.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 41.34/29.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 41.34/29.97  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 41.34/29.97  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 41.34/29.97  tff('#skF_5', type, '#skF_5': $i).
% 41.34/29.97  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 41.34/29.97  tff('#skF_2', type, '#skF_2': $i).
% 41.34/29.97  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 41.34/29.97  tff('#skF_3', type, '#skF_3': $i).
% 41.34/29.97  tff('#skF_1', type, '#skF_1': $i).
% 41.34/29.97  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 41.34/29.97  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 41.34/29.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 41.34/29.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 41.34/29.97  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 41.34/29.97  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 41.34/29.97  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 41.34/29.97  tff('#skF_4', type, '#skF_4': $i).
% 41.34/29.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 41.34/29.97  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 41.34/29.97  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 41.34/29.97  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 41.34/29.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 41.34/29.97  
% 41.34/30.00  tff(f_251, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (r1_tarski(k7_relset_1(A, B, C, D), E) <=> r1_tarski(D, k8_relset_1(A, B, C, E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_2)).
% 41.34/30.00  tff(f_67, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 41.34/30.00  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 41.34/30.00  tff(f_94, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 41.34/30.00  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 41.34/30.00  tff(f_156, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 41.34/30.00  tff(f_152, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 41.34/30.00  tff(f_182, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 41.34/30.00  tff(f_160, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 41.34/30.00  tff(f_214, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_2)).
% 41.34/30.00  tff(f_125, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 41.34/30.00  tff(f_226, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 41.34/30.00  tff(f_168, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 41.34/30.00  tff(f_102, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k9_relat_1(B, k1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_relat_1)).
% 41.34/30.00  tff(f_98, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 41.34/30.00  tff(f_135, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 41.34/30.00  tff(f_92, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 41.34/30.00  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 41.34/30.00  tff(f_48, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 41.34/30.00  tff(f_148, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 41.34/30.00  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 41.34/30.00  tff(f_73, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 41.34/30.00  tff(f_202, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => ((v1_funct_1(C) & ~v1_xboole_0(C)) & v1_funct_2(C, A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_funct_2)).
% 41.34/30.00  tff(f_108, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 41.34/30.00  tff(f_42, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 41.34/30.00  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 41.34/30.00  tff(c_104, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_251])).
% 41.34/30.00  tff(c_96, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_251])).
% 41.34/30.00  tff(c_156, plain, (![A_120, B_121]: (r1_tarski(A_120, B_121) | ~m1_subset_1(A_120, k1_zfmisc_1(B_121)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 41.34/30.00  tff(c_171, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_96, c_156])).
% 41.34/30.00  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 41.34/30.00  tff(c_44, plain, (![A_27, B_28]: (v1_relat_1(k2_zfmisc_1(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 41.34/30.00  tff(c_98, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_251])).
% 41.34/30.00  tff(c_89827, plain, (![B_2728, A_2729]: (v1_relat_1(B_2728) | ~m1_subset_1(B_2728, k1_zfmisc_1(A_2729)) | ~v1_relat_1(A_2729))), inference(cnfTransformation, [status(thm)], [f_80])).
% 41.34/30.00  tff(c_89833, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_98, c_89827])).
% 41.34/30.00  tff(c_89846, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_89833])).
% 41.34/30.00  tff(c_102, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_251])).
% 41.34/30.00  tff(c_142556, plain, (![A_4653, B_4654, C_4655, D_4656]: (k7_relset_1(A_4653, B_4654, C_4655, D_4656)=k9_relat_1(C_4655, D_4656) | ~m1_subset_1(C_4655, k1_zfmisc_1(k2_zfmisc_1(A_4653, B_4654))))), inference(cnfTransformation, [status(thm)], [f_156])).
% 41.34/30.00  tff(c_142570, plain, (![D_4656]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_4656)=k9_relat_1('#skF_3', D_4656))), inference(resolution, [status(thm)], [c_98, c_142556])).
% 41.34/30.00  tff(c_141905, plain, (![A_4597, B_4598, C_4599]: (k2_relset_1(A_4597, B_4598, C_4599)=k2_relat_1(C_4599) | ~m1_subset_1(C_4599, k1_zfmisc_1(k2_zfmisc_1(A_4597, B_4598))))), inference(cnfTransformation, [status(thm)], [f_152])).
% 41.34/30.00  tff(c_141924, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_98, c_141905])).
% 41.34/30.00  tff(c_142837, plain, (![A_4673, B_4674, C_4675]: (k7_relset_1(A_4673, B_4674, C_4675, A_4673)=k2_relset_1(A_4673, B_4674, C_4675) | ~m1_subset_1(C_4675, k1_zfmisc_1(k2_zfmisc_1(A_4673, B_4674))))), inference(cnfTransformation, [status(thm)], [f_182])).
% 41.34/30.00  tff(c_142842, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_98, c_142837])).
% 41.34/30.00  tff(c_142852, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_142570, c_141924, c_142842])).
% 41.34/30.00  tff(c_100, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_251])).
% 41.34/30.00  tff(c_142405, plain, (![A_4635, B_4636, C_4637, D_4638]: (k8_relset_1(A_4635, B_4636, C_4637, D_4638)=k10_relat_1(C_4637, D_4638) | ~m1_subset_1(C_4637, k1_zfmisc_1(k2_zfmisc_1(A_4635, B_4636))))), inference(cnfTransformation, [status(thm)], [f_160])).
% 41.34/30.00  tff(c_142419, plain, (![D_4638]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_4638)=k10_relat_1('#skF_3', D_4638))), inference(resolution, [status(thm)], [c_98, c_142405])).
% 41.34/30.00  tff(c_144839, plain, (![B_4770, A_4771, C_4772]: (k1_xboole_0=B_4770 | k8_relset_1(A_4771, B_4770, C_4772, B_4770)=A_4771 | ~m1_subset_1(C_4772, k1_zfmisc_1(k2_zfmisc_1(A_4771, B_4770))) | ~v1_funct_2(C_4772, A_4771, B_4770) | ~v1_funct_1(C_4772))), inference(cnfTransformation, [status(thm)], [f_214])).
% 41.34/30.00  tff(c_144850, plain, (k1_xboole_0='#skF_2' | k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_98, c_144839])).
% 41.34/30.00  tff(c_144864, plain, (k1_xboole_0='#skF_2' | k10_relat_1('#skF_3', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_142419, c_144850])).
% 41.34/30.00  tff(c_144868, plain, (k10_relat_1('#skF_3', '#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_144864])).
% 41.34/30.00  tff(c_54, plain, (![B_42, A_41]: (r1_tarski(k9_relat_1(B_42, k10_relat_1(B_42, A_41)), A_41) | ~v1_funct_1(B_42) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_125])).
% 41.34/30.00  tff(c_144873, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_144868, c_54])).
% 41.34/30.00  tff(c_144877, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_89846, c_102, c_142852, c_144873])).
% 41.34/30.00  tff(c_90, plain, (![B_83, A_82]: (v1_funct_2(B_83, k1_relat_1(B_83), A_82) | ~r1_tarski(k2_relat_1(B_83), A_82) | ~v1_funct_1(B_83) | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_226])).
% 41.34/30.00  tff(c_143683, plain, (![C_4706, A_4707, B_4708]: (m1_subset_1(C_4706, k1_zfmisc_1(k2_zfmisc_1(A_4707, B_4708))) | ~r1_tarski(k2_relat_1(C_4706), B_4708) | ~r1_tarski(k1_relat_1(C_4706), A_4707) | ~v1_relat_1(C_4706))), inference(cnfTransformation, [status(thm)], [f_168])).
% 41.34/30.00  tff(c_28, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 41.34/30.00  tff(c_170835, plain, (![C_5577, A_5578, B_5579]: (r1_tarski(C_5577, k2_zfmisc_1(A_5578, B_5579)) | ~r1_tarski(k2_relat_1(C_5577), B_5579) | ~r1_tarski(k1_relat_1(C_5577), A_5578) | ~v1_relat_1(C_5577))), inference(resolution, [status(thm)], [c_143683, c_28])).
% 41.34/30.00  tff(c_170867, plain, (![A_5578]: (r1_tarski('#skF_3', k2_zfmisc_1(A_5578, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_5578) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_144877, c_170835])).
% 41.34/30.00  tff(c_170928, plain, (![A_5580]: (r1_tarski('#skF_3', k2_zfmisc_1(A_5580, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_5580))), inference(demodulation, [status(thm), theory('equality')], [c_89846, c_170867])).
% 41.34/30.00  tff(c_171022, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_8, c_170928])).
% 41.34/30.00  tff(c_30, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_67])).
% 41.34/30.00  tff(c_142418, plain, (![A_4635, B_4636, A_15, D_4638]: (k8_relset_1(A_4635, B_4636, A_15, D_4638)=k10_relat_1(A_15, D_4638) | ~r1_tarski(A_15, k2_zfmisc_1(A_4635, B_4636)))), inference(resolution, [status(thm)], [c_30, c_142405])).
% 41.34/30.00  tff(c_171066, plain, (![D_4638]: (k8_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3', D_4638)=k10_relat_1('#skF_3', D_4638))), inference(resolution, [status(thm)], [c_171022, c_142418])).
% 41.34/30.00  tff(c_178649, plain, (![B_5833, A_5834, A_5835]: (k1_xboole_0=B_5833 | k8_relset_1(A_5834, B_5833, A_5835, B_5833)=A_5834 | ~v1_funct_2(A_5835, A_5834, B_5833) | ~v1_funct_1(A_5835) | ~r1_tarski(A_5835, k2_zfmisc_1(A_5834, B_5833)))), inference(resolution, [status(thm)], [c_30, c_144839])).
% 41.34/30.00  tff(c_178661, plain, (k1_xboole_0='#skF_2' | k8_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_171022, c_178649])).
% 41.34/30.00  tff(c_178719, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_144868, c_171066, c_178661])).
% 41.34/30.00  tff(c_179430, plain, (~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_178719])).
% 41.34/30.00  tff(c_179440, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_90, c_179430])).
% 41.34/30.00  tff(c_179444, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89846, c_102, c_144877, c_179440])).
% 41.34/30.00  tff(c_179445, plain, (k1_relat_1('#skF_3')='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_178719])).
% 41.34/30.00  tff(c_179447, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_179445])).
% 41.34/30.00  tff(c_48, plain, (![B_32, A_31]: (r1_tarski(k9_relat_1(B_32, A_31), k9_relat_1(B_32, k1_relat_1(B_32))) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_102])).
% 41.34/30.00  tff(c_142876, plain, (r1_tarski(k2_relat_1('#skF_3'), k9_relat_1('#skF_3', k1_relat_1('#skF_3'))) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_142852, c_48])).
% 41.34/30.00  tff(c_142889, plain, (r1_tarski(k2_relat_1('#skF_3'), k9_relat_1('#skF_3', k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_89846, c_142876])).
% 41.34/30.00  tff(c_140928, plain, (![B_4502, A_4503]: (r1_tarski(k9_relat_1(B_4502, A_4503), k2_relat_1(B_4502)) | ~v1_relat_1(B_4502))), inference(cnfTransformation, [status(thm)], [f_98])).
% 41.34/30.00  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 41.34/30.00  tff(c_165870, plain, (![B_5458, A_5459]: (k9_relat_1(B_5458, A_5459)=k2_relat_1(B_5458) | ~r1_tarski(k2_relat_1(B_5458), k9_relat_1(B_5458, A_5459)) | ~v1_relat_1(B_5458))), inference(resolution, [status(thm)], [c_140928, c_4])).
% 41.34/30.00  tff(c_165884, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_142889, c_165870])).
% 41.34/30.00  tff(c_165916, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_89846, c_165884])).
% 41.34/30.00  tff(c_56, plain, (![A_43, C_45, B_44]: (r1_tarski(A_43, k10_relat_1(C_45, B_44)) | ~r1_tarski(k9_relat_1(C_45, A_43), B_44) | ~r1_tarski(A_43, k1_relat_1(C_45)) | ~v1_funct_1(C_45) | ~v1_relat_1(C_45))), inference(cnfTransformation, [status(thm)], [f_135])).
% 41.34/30.00  tff(c_165960, plain, (![B_44]: (r1_tarski(k1_relat_1('#skF_3'), k10_relat_1('#skF_3', B_44)) | ~r1_tarski(k2_relat_1('#skF_3'), B_44) | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_165916, c_56])).
% 41.34/30.00  tff(c_169277, plain, (![B_5535]: (r1_tarski(k1_relat_1('#skF_3'), k10_relat_1('#skF_3', B_5535)) | ~r1_tarski(k2_relat_1('#skF_3'), B_5535))), inference(demodulation, [status(thm), theory('equality')], [c_89846, c_102, c_8, c_165960])).
% 41.34/30.00  tff(c_42, plain, (![B_26, A_25]: (r1_tarski(k2_relat_1(B_26), A_25) | ~v5_relat_1(B_26, A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_92])).
% 41.34/30.00  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 41.34/30.00  tff(c_16, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 41.34/30.00  tff(c_141643, plain, (![C_4574, B_4575, A_4576]: (v1_xboole_0(C_4574) | ~m1_subset_1(C_4574, k1_zfmisc_1(k2_zfmisc_1(B_4575, A_4576))) | ~v1_xboole_0(A_4576))), inference(cnfTransformation, [status(thm)], [f_148])).
% 41.34/30.00  tff(c_141660, plain, (![C_4574]: (v1_xboole_0(C_4574) | ~m1_subset_1(C_4574, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_141643])).
% 41.34/30.00  tff(c_141667, plain, (![C_4577]: (v1_xboole_0(C_4577) | ~m1_subset_1(C_4577, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_141660])).
% 41.34/30.00  tff(c_141679, plain, (![A_4578]: (v1_xboole_0(A_4578) | ~r1_tarski(A_4578, k1_xboole_0))), inference(resolution, [status(thm)], [c_30, c_141667])).
% 41.34/30.00  tff(c_141697, plain, (![B_26]: (v1_xboole_0(k2_relat_1(B_26)) | ~v5_relat_1(B_26, k1_xboole_0) | ~v1_relat_1(B_26))), inference(resolution, [status(thm)], [c_42, c_141679])).
% 41.34/30.00  tff(c_26, plain, (![A_13, B_14]: (r2_hidden(A_13, B_14) | v1_xboole_0(B_14) | ~m1_subset_1(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 41.34/30.00  tff(c_141479, plain, (![A_4553, C_4554, B_4555]: (m1_subset_1(A_4553, C_4554) | ~m1_subset_1(B_4555, k1_zfmisc_1(C_4554)) | ~r2_hidden(A_4553, B_4555))), inference(cnfTransformation, [status(thm)], [f_73])).
% 41.34/30.00  tff(c_141791, plain, (![A_4584, B_4585, A_4586]: (m1_subset_1(A_4584, B_4585) | ~r2_hidden(A_4584, A_4586) | ~r1_tarski(A_4586, B_4585))), inference(resolution, [status(thm)], [c_30, c_141479])).
% 41.34/30.00  tff(c_141794, plain, (![A_13, B_4585, B_14]: (m1_subset_1(A_13, B_4585) | ~r1_tarski(B_14, B_4585) | v1_xboole_0(B_14) | ~m1_subset_1(A_13, B_14))), inference(resolution, [status(thm)], [c_26, c_141791])).
% 41.34/30.00  tff(c_144900, plain, (![A_13]: (m1_subset_1(A_13, '#skF_2') | v1_xboole_0(k2_relat_1('#skF_3')) | ~m1_subset_1(A_13, k2_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_144877, c_141794])).
% 41.34/30.00  tff(c_145564, plain, (v1_xboole_0(k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_144900])).
% 41.34/30.00  tff(c_106, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_251])).
% 41.34/30.00  tff(c_144072, plain, (![C_4732, A_4733, B_4734]: (~v1_xboole_0(C_4732) | ~v1_funct_2(C_4732, A_4733, B_4734) | ~v1_funct_1(C_4732) | ~m1_subset_1(C_4732, k1_zfmisc_1(k2_zfmisc_1(A_4733, B_4734))) | v1_xboole_0(B_4734) | v1_xboole_0(A_4733))), inference(cnfTransformation, [status(thm)], [f_202])).
% 41.34/30.00  tff(c_144085, plain, (~v1_xboole_0('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_98, c_144072])).
% 41.34/30.00  tff(c_144101, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_144085])).
% 41.34/30.00  tff(c_144102, plain, (~v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_106, c_104, c_144101])).
% 41.34/30.00  tff(c_50, plain, (![C_35, A_33, B_34]: (r1_tarski(k9_relat_1(C_35, A_33), k9_relat_1(C_35, B_34)) | ~r1_tarski(A_33, B_34) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_108])).
% 41.34/30.00  tff(c_142867, plain, (![B_34]: (r1_tarski(k2_relat_1('#skF_3'), k9_relat_1('#skF_3', B_34)) | ~r1_tarski('#skF_1', B_34) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_142852, c_50])).
% 41.34/30.00  tff(c_142883, plain, (![B_34]: (r1_tarski(k2_relat_1('#skF_3'), k9_relat_1('#skF_3', B_34)) | ~r1_tarski('#skF_1', B_34))), inference(demodulation, [status(thm), theory('equality')], [c_89846, c_142867])).
% 41.34/30.00  tff(c_143369, plain, (![B_4693, A_4694]: (m1_subset_1(B_4693, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_4693), A_4694))) | ~r1_tarski(k2_relat_1(B_4693), A_4694) | ~v1_funct_1(B_4693) | ~v1_relat_1(B_4693))), inference(cnfTransformation, [status(thm)], [f_226])).
% 41.34/30.00  tff(c_62, plain, (![C_52, B_50, A_49]: (v1_xboole_0(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(B_50, A_49))) | ~v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_148])).
% 41.34/30.00  tff(c_146446, plain, (![B_4841, A_4842]: (v1_xboole_0(B_4841) | ~v1_xboole_0(A_4842) | ~r1_tarski(k2_relat_1(B_4841), A_4842) | ~v1_funct_1(B_4841) | ~v1_relat_1(B_4841))), inference(resolution, [status(thm)], [c_143369, c_62])).
% 41.34/30.00  tff(c_146472, plain, (![B_34]: (v1_xboole_0('#skF_3') | ~v1_xboole_0(k9_relat_1('#skF_3', B_34)) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~r1_tarski('#skF_1', B_34))), inference(resolution, [status(thm)], [c_142883, c_146446])).
% 41.34/30.00  tff(c_146516, plain, (![B_34]: (v1_xboole_0('#skF_3') | ~v1_xboole_0(k9_relat_1('#skF_3', B_34)) | ~r1_tarski('#skF_1', B_34))), inference(demodulation, [status(thm), theory('equality')], [c_89846, c_102, c_146472])).
% 41.34/30.00  tff(c_146530, plain, (![B_4843]: (~v1_xboole_0(k9_relat_1('#skF_3', B_4843)) | ~r1_tarski('#skF_1', B_4843))), inference(negUnitSimplification, [status(thm)], [c_144102, c_146516])).
% 41.34/30.00  tff(c_146537, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_142852, c_146530])).
% 41.34/30.00  tff(c_146547, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_145564, c_146537])).
% 41.34/30.00  tff(c_146549, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_144900])).
% 41.34/30.00  tff(c_146552, plain, (~v5_relat_1('#skF_3', k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_141697, c_146549])).
% 41.34/30.00  tff(c_146555, plain, (~v5_relat_1('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_89846, c_146552])).
% 41.34/30.00  tff(c_141722, plain, (![B_4582, A_4583]: (r1_tarski(k9_relat_1(B_4582, k10_relat_1(B_4582, A_4583)), A_4583) | ~v1_funct_1(B_4582) | ~v1_relat_1(B_4582))), inference(cnfTransformation, [status(thm)], [f_125])).
% 41.34/30.00  tff(c_12, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_42])).
% 41.34/30.00  tff(c_141788, plain, (![B_4582]: (k9_relat_1(B_4582, k10_relat_1(B_4582, k1_xboole_0))=k1_xboole_0 | ~v1_funct_1(B_4582) | ~v1_relat_1(B_4582))), inference(resolution, [status(thm)], [c_141722, c_12])).
% 41.34/30.00  tff(c_165983, plain, (![B_34]: (r1_tarski(k2_relat_1('#skF_3'), k9_relat_1('#skF_3', B_34)) | ~r1_tarski(k1_relat_1('#skF_3'), B_34) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_165916, c_50])).
% 41.34/30.00  tff(c_167232, plain, (![B_5489]: (r1_tarski(k2_relat_1('#skF_3'), k9_relat_1('#skF_3', B_5489)) | ~r1_tarski(k1_relat_1('#skF_3'), B_5489))), inference(demodulation, [status(thm), theory('equality')], [c_89846, c_165983])).
% 41.34/30.00  tff(c_40, plain, (![B_26, A_25]: (v5_relat_1(B_26, A_25) | ~r1_tarski(k2_relat_1(B_26), A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_92])).
% 41.34/30.00  tff(c_167270, plain, (![B_5489]: (v5_relat_1('#skF_3', k9_relat_1('#skF_3', B_5489)) | ~v1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), B_5489))), inference(resolution, [status(thm)], [c_167232, c_40])).
% 41.34/30.00  tff(c_168274, plain, (![B_5511]: (v5_relat_1('#skF_3', k9_relat_1('#skF_3', B_5511)) | ~r1_tarski(k1_relat_1('#skF_3'), B_5511))), inference(demodulation, [status(thm), theory('equality')], [c_89846, c_167270])).
% 41.34/30.00  tff(c_168292, plain, (v5_relat_1('#skF_3', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_3'), k10_relat_1('#skF_3', k1_xboole_0)) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_141788, c_168274])).
% 41.34/30.00  tff(c_168303, plain, (v5_relat_1('#skF_3', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_3'), k10_relat_1('#skF_3', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_89846, c_102, c_168292])).
% 41.34/30.00  tff(c_168304, plain, (~r1_tarski(k1_relat_1('#skF_3'), k10_relat_1('#skF_3', k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_146555, c_168303])).
% 41.34/30.00  tff(c_169319, plain, (~r1_tarski(k2_relat_1('#skF_3'), k1_xboole_0)), inference(resolution, [status(thm)], [c_169277, c_168304])).
% 41.34/30.00  tff(c_179497, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_179447, c_169319])).
% 41.34/30.00  tff(c_179580, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_144877, c_179497])).
% 41.34/30.00  tff(c_179581, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_179445])).
% 41.34/30.00  tff(c_46, plain, (![B_30, A_29]: (r1_tarski(k9_relat_1(B_30, A_29), k2_relat_1(B_30)) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_98])).
% 41.34/30.00  tff(c_10, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 41.34/30.00  tff(c_144928, plain, (![A_4775]: (r1_tarski(A_4775, '#skF_2') | ~r1_tarski(A_4775, k2_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_144877, c_10])).
% 41.34/30.00  tff(c_144955, plain, (![A_29]: (r1_tarski(k9_relat_1('#skF_3', A_29), '#skF_2') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_144928])).
% 41.34/30.00  tff(c_144979, plain, (![A_4776]: (r1_tarski(k9_relat_1('#skF_3', A_4776), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_89846, c_144955])).
% 41.34/30.00  tff(c_144988, plain, (![A_4776]: (r1_tarski(A_4776, k10_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(A_4776, k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_144979, c_56])).
% 41.34/30.00  tff(c_145064, plain, (![A_4779]: (r1_tarski(A_4779, '#skF_1') | ~r1_tarski(A_4779, k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_89846, c_102, c_144868, c_144988])).
% 41.34/30.00  tff(c_145100, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_8, c_145064])).
% 41.34/30.00  tff(c_145131, plain, (k1_relat_1('#skF_3')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_145100, c_4])).
% 41.34/30.00  tff(c_145133, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_145131])).
% 41.34/30.00  tff(c_179627, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_179581, c_145133])).
% 41.34/30.00  tff(c_179642, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_179627])).
% 41.34/30.00  tff(c_179643, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_145131])).
% 41.34/30.00  tff(c_232, plain, (![B_133, A_134]: (v1_relat_1(B_133) | ~m1_subset_1(B_133, k1_zfmisc_1(A_134)) | ~v1_relat_1(A_134))), inference(cnfTransformation, [status(thm)], [f_80])).
% 41.34/30.00  tff(c_238, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_98, c_232])).
% 41.34/30.00  tff(c_251, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_238])).
% 41.34/30.00  tff(c_1927, plain, (![A_289, B_290, C_291, D_292]: (k8_relset_1(A_289, B_290, C_291, D_292)=k10_relat_1(C_291, D_292) | ~m1_subset_1(C_291, k1_zfmisc_1(k2_zfmisc_1(A_289, B_290))))), inference(cnfTransformation, [status(thm)], [f_160])).
% 41.34/30.00  tff(c_1941, plain, (![D_292]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_292)=k10_relat_1('#skF_3', D_292))), inference(resolution, [status(thm)], [c_98, c_1927])).
% 41.34/30.00  tff(c_114, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5') | r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_251])).
% 41.34/30.00  tff(c_180, plain, (r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_114])).
% 41.34/30.00  tff(c_1946, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1941, c_180])).
% 41.34/30.00  tff(c_1069, plain, (![B_224, A_225]: (r1_tarski(k9_relat_1(B_224, k10_relat_1(B_224, A_225)), A_225) | ~v1_funct_1(B_224) | ~v1_relat_1(B_224))), inference(cnfTransformation, [status(thm)], [f_125])).
% 41.34/30.00  tff(c_47687, plain, (![A_1643, A_1644, B_1645]: (r1_tarski(A_1643, A_1644) | ~r1_tarski(A_1643, k9_relat_1(B_1645, k10_relat_1(B_1645, A_1644))) | ~v1_funct_1(B_1645) | ~v1_relat_1(B_1645))), inference(resolution, [status(thm)], [c_1069, c_10])).
% 41.34/30.00  tff(c_89257, plain, (![C_2719, A_2720, A_2721]: (r1_tarski(k9_relat_1(C_2719, A_2720), A_2721) | ~v1_funct_1(C_2719) | ~r1_tarski(A_2720, k10_relat_1(C_2719, A_2721)) | ~v1_relat_1(C_2719))), inference(resolution, [status(thm)], [c_50, c_47687])).
% 41.34/30.00  tff(c_1797, plain, (![A_277, B_278, C_279, D_280]: (k7_relset_1(A_277, B_278, C_279, D_280)=k9_relat_1(C_279, D_280) | ~m1_subset_1(C_279, k1_zfmisc_1(k2_zfmisc_1(A_277, B_278))))), inference(cnfTransformation, [status(thm)], [f_156])).
% 41.34/30.00  tff(c_1811, plain, (![D_280]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_280)=k9_relat_1('#skF_3', D_280))), inference(resolution, [status(thm)], [c_98, c_1797])).
% 41.34/30.00  tff(c_108, plain, (~r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_251])).
% 41.34/30.00  tff(c_219, plain, (~r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_180, c_108])).
% 41.34/30.00  tff(c_1821, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1811, c_219])).
% 41.34/30.00  tff(c_89617, plain, (~v1_funct_1('#skF_3') | ~r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_89257, c_1821])).
% 41.34/30.00  tff(c_89797, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_251, c_1946, c_102, c_89617])).
% 41.34/30.00  tff(c_89799, plain, (~r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_114])).
% 41.34/30.00  tff(c_142421, plain, (~r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_142419, c_89799])).
% 41.34/30.00  tff(c_89798, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_114])).
% 41.34/30.00  tff(c_142585, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_142570, c_89798])).
% 41.34/30.00  tff(c_144122, plain, (![A_4737, C_4738, B_4739]: (r1_tarski(A_4737, k10_relat_1(C_4738, B_4739)) | ~r1_tarski(k9_relat_1(C_4738, A_4737), B_4739) | ~r1_tarski(A_4737, k1_relat_1(C_4738)) | ~v1_funct_1(C_4738) | ~v1_relat_1(C_4738))), inference(cnfTransformation, [status(thm)], [f_135])).
% 41.34/30.00  tff(c_144150, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_142585, c_144122])).
% 41.34/30.00  tff(c_144200, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_89846, c_102, c_144150])).
% 41.34/30.00  tff(c_144201, plain, (~r1_tarski('#skF_4', k1_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_142421, c_144200])).
% 41.34/30.00  tff(c_179657, plain, (~r1_tarski('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_179643, c_144201])).
% 41.34/30.00  tff(c_179665, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_171, c_179657])).
% 41.34/30.00  tff(c_179666, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_144864])).
% 41.34/30.00  tff(c_179725, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_179666, c_2])).
% 41.34/30.00  tff(c_179728, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_179725])).
% 41.34/30.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 41.34/30.00  
% 41.34/30.00  Inference rules
% 41.34/30.00  ----------------------
% 41.34/30.00  #Ref     : 0
% 41.34/30.00  #Sup     : 38646
% 41.34/30.00  #Fact    : 0
% 41.34/30.00  #Define  : 0
% 41.34/30.00  #Split   : 289
% 41.34/30.00  #Chain   : 0
% 41.34/30.00  #Close   : 0
% 41.34/30.00  
% 41.34/30.00  Ordering : KBO
% 41.34/30.00  
% 41.34/30.00  Simplification rules
% 41.34/30.00  ----------------------
% 41.34/30.00  #Subsume      : 12659
% 41.34/30.00  #Demod        : 23535
% 41.34/30.00  #Tautology    : 5777
% 41.34/30.00  #SimpNegUnit  : 1362
% 41.34/30.00  #BackRed      : 1813
% 41.34/30.00  
% 41.34/30.00  #Partial instantiations: 0
% 41.34/30.00  #Strategies tried      : 1
% 41.34/30.00  
% 41.34/30.00  Timing (in seconds)
% 41.34/30.00  ----------------------
% 41.34/30.00  Preprocessing        : 0.40
% 41.34/30.00  Parsing              : 0.21
% 41.34/30.00  CNF conversion       : 0.03
% 41.34/30.00  Main loop            : 28.81
% 41.34/30.00  Inferencing          : 5.32
% 41.34/30.00  Reduction            : 11.67
% 41.34/30.00  Demodulation         : 8.56
% 41.34/30.00  BG Simplification    : 0.43
% 41.34/30.00  Subsumption          : 9.20
% 41.34/30.00  Abstraction          : 0.68
% 41.34/30.00  MUC search           : 0.00
% 41.34/30.00  Cooper               : 0.00
% 41.34/30.00  Total                : 29.27
% 41.34/30.00  Index Insertion      : 0.00
% 41.34/30.01  Index Deletion       : 0.00
% 41.34/30.01  Index Matching       : 0.00
% 41.34/30.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
