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
% DateTime   : Thu Dec  3 10:26:53 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 290 expanded)
%              Number of leaves         :   50 ( 122 expanded)
%              Depth                    :   15
%              Number of atoms          :  250 (1131 expanded)
%              Number of equality atoms :   26 (  91 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(r1_funct_2,type,(
    r1_funct_2: ( $i * $i * $i * $i * $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_197,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,B) )
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,u1_struct_0(B),u1_struct_0(A))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
                   => ( g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                     => r1_funct_2(u1_struct_0(B),u1_struct_0(A),u1_struct_0(C),u1_struct_0(A),D,k2_tmap_1(B,A,D,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_tmap_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_126,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(B)
        & ~ v1_xboole_0(D)
        & v1_funct_1(E)
        & v1_funct_2(E,A,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,C,D)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( r1_funct_2(A,B,C,D,E,F)
      <=> E = F ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

tff(f_88,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_164,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_160,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_41,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_153,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

tff(c_76,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_34,plain,(
    ! [A_23] :
      ( l1_struct_0(A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_64,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_62,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_60,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_416,plain,(
    ! [F_129,A_127,B_130,D_128,C_131] :
      ( r1_funct_2(A_127,B_130,C_131,D_128,F_129,F_129)
      | ~ m1_subset_1(F_129,k1_zfmisc_1(k2_zfmisc_1(C_131,D_128)))
      | ~ v1_funct_2(F_129,C_131,D_128)
      | ~ m1_subset_1(F_129,k1_zfmisc_1(k2_zfmisc_1(A_127,B_130)))
      | ~ v1_funct_2(F_129,A_127,B_130)
      | ~ v1_funct_1(F_129)
      | v1_xboole_0(D_128)
      | v1_xboole_0(B_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_418,plain,(
    ! [A_127,B_130] :
      ( r1_funct_2(A_127,B_130,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6','#skF_6')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_127,B_130)))
      | ~ v1_funct_2('#skF_6',A_127,B_130)
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(B_130) ) ),
    inference(resolution,[status(thm)],[c_60,c_416])).

tff(c_421,plain,(
    ! [A_127,B_130] :
      ( r1_funct_2(A_127,B_130,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6','#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_127,B_130)))
      | ~ v1_funct_2('#skF_6',A_127,B_130)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(B_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_418])).

tff(c_840,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_421])).

tff(c_38,plain,(
    ! [A_27] :
      ( ~ v1_xboole_0(u1_struct_0(A_27))
      | ~ l1_struct_0(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_843,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_840,c_38])).

tff(c_846,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_843])).

tff(c_849,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_846])).

tff(c_853,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_849])).

tff(c_855,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_421])).

tff(c_856,plain,(
    ! [A_166,B_167] :
      ( r1_funct_2(A_166,B_167,u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6','#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_166,B_167)))
      | ~ v1_funct_2('#skF_6',A_166,B_167)
      | v1_xboole_0(B_167) ) ),
    inference(splitRight,[status(thm)],[c_421])).

tff(c_66,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_127,plain,(
    ! [C_87,A_88,B_89] :
      ( v1_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_131,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_127])).

tff(c_132,plain,(
    ! [C_90,A_91,B_92] :
      ( v4_relat_1(C_90,A_91)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_136,plain,(
    v4_relat_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_60,c_132])).

tff(c_146,plain,(
    ! [B_96,A_97] :
      ( k7_relat_1(B_96,A_97) = B_96
      | ~ v4_relat_1(B_96,A_97)
      | ~ v1_relat_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_149,plain,
    ( k7_relat_1('#skF_6',u1_struct_0('#skF_4')) = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_136,c_146])).

tff(c_152,plain,(
    k7_relat_1('#skF_6',u1_struct_0('#skF_4')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_149])).

tff(c_70,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_54,plain,(
    ! [A_58] :
      ( m1_pre_topc(A_58,A_58)
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_210,plain,(
    ! [A_113,B_114] :
      ( m1_pre_topc(A_113,g1_pre_topc(u1_struct_0(B_114),u1_pre_topc(B_114)))
      | ~ m1_pre_topc(A_113,B_114)
      | ~ l1_pre_topc(B_114)
      | ~ l1_pre_topc(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_92,plain,(
    ! [B_78,A_79] :
      ( l1_pre_topc(B_78)
      | ~ m1_pre_topc(B_78,A_79)
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_98,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_92])).

tff(c_102,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_98])).

tff(c_58,plain,(
    g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_166,plain,(
    ! [B_102,A_103] :
      ( m1_pre_topc(B_102,A_103)
      | ~ m1_pre_topc(B_102,g1_pre_topc(u1_struct_0(A_103),u1_pre_topc(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_169,plain,(
    ! [B_102] :
      ( m1_pre_topc(B_102,'#skF_5')
      | ~ m1_pre_topc(B_102,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_166])).

tff(c_175,plain,(
    ! [B_102] :
      ( m1_pre_topc(B_102,'#skF_5')
      | ~ m1_pre_topc(B_102,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_169])).

tff(c_214,plain,(
    ! [A_113] :
      ( m1_pre_topc(A_113,'#skF_5')
      | ~ m1_pre_topc(A_113,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_113) ) ),
    inference(resolution,[status(thm)],[c_210,c_175])).

tff(c_226,plain,(
    ! [A_113] :
      ( m1_pre_topc(A_113,'#skF_5')
      | ~ m1_pre_topc(A_113,'#skF_4')
      | ~ l1_pre_topc(A_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_214])).

tff(c_157,plain,(
    ! [B_98,A_99] :
      ( m1_subset_1(u1_struct_0(B_98),k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ m1_pre_topc(B_98,A_99)
      | ~ l1_pre_topc(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_20,plain,(
    ! [A_8] : ~ v1_xboole_0(k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_104,plain,(
    ! [A_81,B_82] :
      ( r2_hidden(A_81,B_82)
      | v1_xboole_0(B_82)
      | ~ m1_subset_1(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [C_7,A_3] :
      ( r1_tarski(C_7,A_3)
      | ~ r2_hidden(C_7,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_108,plain,(
    ! [A_81,A_3] :
      ( r1_tarski(A_81,A_3)
      | v1_xboole_0(k1_zfmisc_1(A_3))
      | ~ m1_subset_1(A_81,k1_zfmisc_1(A_3)) ) ),
    inference(resolution,[status(thm)],[c_104,c_8])).

tff(c_111,plain,(
    ! [A_81,A_3] :
      ( r1_tarski(A_81,A_3)
      | ~ m1_subset_1(A_81,k1_zfmisc_1(A_3)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_108])).

tff(c_161,plain,(
    ! [B_98,A_99] :
      ( r1_tarski(u1_struct_0(B_98),u1_struct_0(A_99))
      | ~ m1_pre_topc(B_98,A_99)
      | ~ l1_pre_topc(A_99) ) ),
    inference(resolution,[status(thm)],[c_157,c_111])).

tff(c_162,plain,(
    ! [B_100,A_101] :
      ( r1_tarski(u1_struct_0(B_100),u1_struct_0(A_101))
      | ~ m1_pre_topc(B_100,A_101)
      | ~ l1_pre_topc(A_101) ) ),
    inference(resolution,[status(thm)],[c_157,c_111])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_265,plain,(
    ! [B_118,A_119] :
      ( u1_struct_0(B_118) = u1_struct_0(A_119)
      | ~ r1_tarski(u1_struct_0(A_119),u1_struct_0(B_118))
      | ~ m1_pre_topc(B_118,A_119)
      | ~ l1_pre_topc(A_119) ) ),
    inference(resolution,[status(thm)],[c_162,c_2])).

tff(c_276,plain,(
    ! [B_120,A_121] :
      ( u1_struct_0(B_120) = u1_struct_0(A_121)
      | ~ m1_pre_topc(A_121,B_120)
      | ~ l1_pre_topc(B_120)
      | ~ m1_pre_topc(B_120,A_121)
      | ~ l1_pre_topc(A_121) ) ),
    inference(resolution,[status(thm)],[c_161,c_265])).

tff(c_286,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_276])).

tff(c_296,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_70,c_286])).

tff(c_297,plain,(
    ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_296])).

tff(c_300,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_226,c_297])).

tff(c_303,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_300])).

tff(c_306,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_303])).

tff(c_310,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_306])).

tff(c_311,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_296])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_72,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_78,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_313,plain,(
    ! [A_122,B_123,C_124,D_125] :
      ( k2_partfun1(A_122,B_123,C_124,D_125) = k7_relat_1(C_124,D_125)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123)))
      | ~ v1_funct_1(C_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_315,plain,(
    ! [D_125] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',D_125) = k7_relat_1('#skF_6',D_125)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_60,c_313])).

tff(c_318,plain,(
    ! [D_125] : k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',D_125) = k7_relat_1('#skF_6',D_125) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_315])).

tff(c_616,plain,(
    ! [A_146,B_147,C_148,D_149] :
      ( k2_partfun1(u1_struct_0(A_146),u1_struct_0(B_147),C_148,u1_struct_0(D_149)) = k2_tmap_1(A_146,B_147,C_148,D_149)
      | ~ m1_pre_topc(D_149,A_146)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_146),u1_struct_0(B_147))))
      | ~ v1_funct_2(C_148,u1_struct_0(A_146),u1_struct_0(B_147))
      | ~ v1_funct_1(C_148)
      | ~ l1_pre_topc(B_147)
      | ~ v2_pre_topc(B_147)
      | v2_struct_0(B_147)
      | ~ l1_pre_topc(A_146)
      | ~ v2_pre_topc(A_146)
      | v2_struct_0(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_622,plain,(
    ! [D_149] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_149)) = k2_tmap_1('#skF_4','#skF_3','#skF_6',D_149)
      | ~ m1_pre_topc(D_149,'#skF_4')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_616])).

tff(c_631,plain,(
    ! [D_149] :
      ( k7_relat_1('#skF_6',u1_struct_0(D_149)) = k2_tmap_1('#skF_4','#skF_3','#skF_6',D_149)
      | ~ m1_pre_topc(D_149,'#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_78,c_76,c_64,c_62,c_318,c_622])).

tff(c_633,plain,(
    ! [D_150] :
      ( k7_relat_1('#skF_6',u1_struct_0(D_150)) = k2_tmap_1('#skF_4','#skF_3','#skF_6',D_150)
      | ~ m1_pre_topc(D_150,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_80,c_631])).

tff(c_645,plain,
    ( k7_relat_1('#skF_6',u1_struct_0('#skF_4')) = k2_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_633])).

tff(c_654,plain,(
    k2_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_152,c_645])).

tff(c_56,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',k2_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_348,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',k2_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_56])).

tff(c_661,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_654,c_348])).

tff(c_859,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_856,c_661])).

tff(c_864,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_859])).

tff(c_866,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_855,c_864])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:30:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.00/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.53  
% 3.00/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.53  %$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.34/1.53  
% 3.34/1.53  %Foreground sorts:
% 3.34/1.53  
% 3.34/1.53  
% 3.34/1.53  %Background operators:
% 3.34/1.53  
% 3.34/1.53  
% 3.34/1.53  %Foreground operators:
% 3.34/1.53  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.34/1.53  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.34/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.34/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.34/1.53  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.34/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.34/1.53  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.34/1.53  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.34/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.34/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.34/1.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.34/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.34/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.34/1.53  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.34/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.34/1.53  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.34/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.34/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.34/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.34/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.34/1.53  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 3.34/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.34/1.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.34/1.53  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.34/1.53  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.34/1.53  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.34/1.53  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.34/1.53  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.34/1.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.34/1.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.34/1.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.34/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.34/1.53  
% 3.34/1.55  tff(f_197, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_tmap_1)).
% 3.34/1.55  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.34/1.55  tff(f_126, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 3.34/1.55  tff(f_88, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.34/1.55  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.34/1.55  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.34/1.55  tff(f_53, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.34/1.55  tff(f_164, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 3.34/1.55  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 3.34/1.55  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.34/1.55  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 3.34/1.55  tff(f_160, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.34/1.55  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.34/1.55  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.34/1.55  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.34/1.55  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.34/1.55  tff(f_69, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.34/1.55  tff(f_153, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.34/1.55  tff(c_76, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.34/1.55  tff(c_34, plain, (![A_23]: (l1_struct_0(A_23) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.34/1.55  tff(c_80, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.34/1.55  tff(c_64, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.34/1.55  tff(c_62, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.34/1.55  tff(c_60, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.34/1.55  tff(c_416, plain, (![F_129, A_127, B_130, D_128, C_131]: (r1_funct_2(A_127, B_130, C_131, D_128, F_129, F_129) | ~m1_subset_1(F_129, k1_zfmisc_1(k2_zfmisc_1(C_131, D_128))) | ~v1_funct_2(F_129, C_131, D_128) | ~m1_subset_1(F_129, k1_zfmisc_1(k2_zfmisc_1(A_127, B_130))) | ~v1_funct_2(F_129, A_127, B_130) | ~v1_funct_1(F_129) | v1_xboole_0(D_128) | v1_xboole_0(B_130))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.34/1.55  tff(c_418, plain, (![A_127, B_130]: (r1_funct_2(A_127, B_130, u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_6', '#skF_6') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_127, B_130))) | ~v1_funct_2('#skF_6', A_127, B_130) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(B_130))), inference(resolution, [status(thm)], [c_60, c_416])).
% 3.34/1.55  tff(c_421, plain, (![A_127, B_130]: (r1_funct_2(A_127, B_130, u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_6', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_127, B_130))) | ~v1_funct_2('#skF_6', A_127, B_130) | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(B_130))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_418])).
% 3.34/1.55  tff(c_840, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_421])).
% 3.34/1.55  tff(c_38, plain, (![A_27]: (~v1_xboole_0(u1_struct_0(A_27)) | ~l1_struct_0(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.34/1.55  tff(c_843, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_840, c_38])).
% 3.34/1.55  tff(c_846, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_80, c_843])).
% 3.34/1.55  tff(c_849, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_846])).
% 3.34/1.55  tff(c_853, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_849])).
% 3.34/1.55  tff(c_855, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_421])).
% 3.34/1.55  tff(c_856, plain, (![A_166, B_167]: (r1_funct_2(A_166, B_167, u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_6', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))) | ~v1_funct_2('#skF_6', A_166, B_167) | v1_xboole_0(B_167))), inference(splitRight, [status(thm)], [c_421])).
% 3.34/1.55  tff(c_66, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.34/1.55  tff(c_127, plain, (![C_87, A_88, B_89]: (v1_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.34/1.55  tff(c_131, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_60, c_127])).
% 3.34/1.55  tff(c_132, plain, (![C_90, A_91, B_92]: (v4_relat_1(C_90, A_91) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.34/1.55  tff(c_136, plain, (v4_relat_1('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_132])).
% 3.34/1.55  tff(c_146, plain, (![B_96, A_97]: (k7_relat_1(B_96, A_97)=B_96 | ~v4_relat_1(B_96, A_97) | ~v1_relat_1(B_96))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.34/1.55  tff(c_149, plain, (k7_relat_1('#skF_6', u1_struct_0('#skF_4'))='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_136, c_146])).
% 3.34/1.55  tff(c_152, plain, (k7_relat_1('#skF_6', u1_struct_0('#skF_4'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_131, c_149])).
% 3.34/1.55  tff(c_70, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.34/1.55  tff(c_54, plain, (![A_58]: (m1_pre_topc(A_58, A_58) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.34/1.55  tff(c_210, plain, (![A_113, B_114]: (m1_pre_topc(A_113, g1_pre_topc(u1_struct_0(B_114), u1_pre_topc(B_114))) | ~m1_pre_topc(A_113, B_114) | ~l1_pre_topc(B_114) | ~l1_pre_topc(A_113))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.34/1.55  tff(c_92, plain, (![B_78, A_79]: (l1_pre_topc(B_78) | ~m1_pre_topc(B_78, A_79) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.34/1.55  tff(c_98, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_66, c_92])).
% 3.34/1.55  tff(c_102, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_98])).
% 3.34/1.55  tff(c_58, plain, (g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))=g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.34/1.55  tff(c_166, plain, (![B_102, A_103]: (m1_pre_topc(B_102, A_103) | ~m1_pre_topc(B_102, g1_pre_topc(u1_struct_0(A_103), u1_pre_topc(A_103))) | ~l1_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.34/1.55  tff(c_169, plain, (![B_102]: (m1_pre_topc(B_102, '#skF_5') | ~m1_pre_topc(B_102, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_166])).
% 3.34/1.55  tff(c_175, plain, (![B_102]: (m1_pre_topc(B_102, '#skF_5') | ~m1_pre_topc(B_102, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_169])).
% 3.34/1.55  tff(c_214, plain, (![A_113]: (m1_pre_topc(A_113, '#skF_5') | ~m1_pre_topc(A_113, '#skF_4') | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_113))), inference(resolution, [status(thm)], [c_210, c_175])).
% 3.34/1.55  tff(c_226, plain, (![A_113]: (m1_pre_topc(A_113, '#skF_5') | ~m1_pre_topc(A_113, '#skF_4') | ~l1_pre_topc(A_113))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_214])).
% 3.34/1.55  tff(c_157, plain, (![B_98, A_99]: (m1_subset_1(u1_struct_0(B_98), k1_zfmisc_1(u1_struct_0(A_99))) | ~m1_pre_topc(B_98, A_99) | ~l1_pre_topc(A_99))), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.34/1.55  tff(c_20, plain, (![A_8]: (~v1_xboole_0(k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.34/1.55  tff(c_104, plain, (![A_81, B_82]: (r2_hidden(A_81, B_82) | v1_xboole_0(B_82) | ~m1_subset_1(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.34/1.55  tff(c_8, plain, (![C_7, A_3]: (r1_tarski(C_7, A_3) | ~r2_hidden(C_7, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.34/1.55  tff(c_108, plain, (![A_81, A_3]: (r1_tarski(A_81, A_3) | v1_xboole_0(k1_zfmisc_1(A_3)) | ~m1_subset_1(A_81, k1_zfmisc_1(A_3)))), inference(resolution, [status(thm)], [c_104, c_8])).
% 3.34/1.55  tff(c_111, plain, (![A_81, A_3]: (r1_tarski(A_81, A_3) | ~m1_subset_1(A_81, k1_zfmisc_1(A_3)))), inference(negUnitSimplification, [status(thm)], [c_20, c_108])).
% 3.34/1.55  tff(c_161, plain, (![B_98, A_99]: (r1_tarski(u1_struct_0(B_98), u1_struct_0(A_99)) | ~m1_pre_topc(B_98, A_99) | ~l1_pre_topc(A_99))), inference(resolution, [status(thm)], [c_157, c_111])).
% 3.34/1.55  tff(c_162, plain, (![B_100, A_101]: (r1_tarski(u1_struct_0(B_100), u1_struct_0(A_101)) | ~m1_pre_topc(B_100, A_101) | ~l1_pre_topc(A_101))), inference(resolution, [status(thm)], [c_157, c_111])).
% 3.34/1.55  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.34/1.55  tff(c_265, plain, (![B_118, A_119]: (u1_struct_0(B_118)=u1_struct_0(A_119) | ~r1_tarski(u1_struct_0(A_119), u1_struct_0(B_118)) | ~m1_pre_topc(B_118, A_119) | ~l1_pre_topc(A_119))), inference(resolution, [status(thm)], [c_162, c_2])).
% 3.34/1.55  tff(c_276, plain, (![B_120, A_121]: (u1_struct_0(B_120)=u1_struct_0(A_121) | ~m1_pre_topc(A_121, B_120) | ~l1_pre_topc(B_120) | ~m1_pre_topc(B_120, A_121) | ~l1_pre_topc(A_121))), inference(resolution, [status(thm)], [c_161, c_265])).
% 3.34/1.55  tff(c_286, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_66, c_276])).
% 3.34/1.55  tff(c_296, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_70, c_286])).
% 3.34/1.55  tff(c_297, plain, (~m1_pre_topc('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_296])).
% 3.34/1.55  tff(c_300, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_226, c_297])).
% 3.34/1.55  tff(c_303, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_300])).
% 3.34/1.55  tff(c_306, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_303])).
% 3.34/1.55  tff(c_310, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_306])).
% 3.34/1.55  tff(c_311, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_296])).
% 3.34/1.55  tff(c_74, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.34/1.55  tff(c_72, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.34/1.55  tff(c_78, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.34/1.55  tff(c_313, plain, (![A_122, B_123, C_124, D_125]: (k2_partfun1(A_122, B_123, C_124, D_125)=k7_relat_1(C_124, D_125) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))) | ~v1_funct_1(C_124))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.34/1.55  tff(c_315, plain, (![D_125]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_6', D_125)=k7_relat_1('#skF_6', D_125) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_60, c_313])).
% 3.34/1.55  tff(c_318, plain, (![D_125]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_6', D_125)=k7_relat_1('#skF_6', D_125))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_315])).
% 3.34/1.55  tff(c_616, plain, (![A_146, B_147, C_148, D_149]: (k2_partfun1(u1_struct_0(A_146), u1_struct_0(B_147), C_148, u1_struct_0(D_149))=k2_tmap_1(A_146, B_147, C_148, D_149) | ~m1_pre_topc(D_149, A_146) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_146), u1_struct_0(B_147)))) | ~v1_funct_2(C_148, u1_struct_0(A_146), u1_struct_0(B_147)) | ~v1_funct_1(C_148) | ~l1_pre_topc(B_147) | ~v2_pre_topc(B_147) | v2_struct_0(B_147) | ~l1_pre_topc(A_146) | ~v2_pre_topc(A_146) | v2_struct_0(A_146))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.34/1.55  tff(c_622, plain, (![D_149]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_149))=k2_tmap_1('#skF_4', '#skF_3', '#skF_6', D_149) | ~m1_pre_topc(D_149, '#skF_4') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_616])).
% 3.34/1.55  tff(c_631, plain, (![D_149]: (k7_relat_1('#skF_6', u1_struct_0(D_149))=k2_tmap_1('#skF_4', '#skF_3', '#skF_6', D_149) | ~m1_pre_topc(D_149, '#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_78, c_76, c_64, c_62, c_318, c_622])).
% 3.34/1.55  tff(c_633, plain, (![D_150]: (k7_relat_1('#skF_6', u1_struct_0(D_150))=k2_tmap_1('#skF_4', '#skF_3', '#skF_6', D_150) | ~m1_pre_topc(D_150, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_74, c_80, c_631])).
% 3.34/1.55  tff(c_645, plain, (k7_relat_1('#skF_6', u1_struct_0('#skF_4'))=k2_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_311, c_633])).
% 3.34/1.55  tff(c_654, plain, (k2_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_152, c_645])).
% 3.34/1.55  tff(c_56, plain, (~r1_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', k2_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.34/1.55  tff(c_348, plain, (~r1_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_6', k2_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_311, c_56])).
% 3.34/1.55  tff(c_661, plain, (~r1_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_654, c_348])).
% 3.34/1.55  tff(c_859, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_856, c_661])).
% 3.34/1.55  tff(c_864, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_859])).
% 3.34/1.55  tff(c_866, plain, $false, inference(negUnitSimplification, [status(thm)], [c_855, c_864])).
% 3.34/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.55  
% 3.34/1.55  Inference rules
% 3.34/1.55  ----------------------
% 3.34/1.55  #Ref     : 0
% 3.34/1.55  #Sup     : 148
% 3.34/1.55  #Fact    : 0
% 3.34/1.55  #Define  : 0
% 3.34/1.55  #Split   : 7
% 3.34/1.55  #Chain   : 0
% 3.34/1.55  #Close   : 0
% 3.34/1.55  
% 3.34/1.55  Ordering : KBO
% 3.34/1.55  
% 3.34/1.55  Simplification rules
% 3.34/1.55  ----------------------
% 3.34/1.55  #Subsume      : 24
% 3.34/1.55  #Demod        : 166
% 3.34/1.55  #Tautology    : 65
% 3.34/1.55  #SimpNegUnit  : 10
% 3.34/1.55  #BackRed      : 3
% 3.34/1.55  
% 3.34/1.55  #Partial instantiations: 0
% 3.34/1.55  #Strategies tried      : 1
% 3.34/1.55  
% 3.34/1.55  Timing (in seconds)
% 3.34/1.55  ----------------------
% 3.34/1.56  Preprocessing        : 0.36
% 3.34/1.56  Parsing              : 0.19
% 3.34/1.56  CNF conversion       : 0.03
% 3.34/1.56  Main loop            : 0.37
% 3.34/1.56  Inferencing          : 0.13
% 3.34/1.56  Reduction            : 0.12
% 3.34/1.56  Demodulation         : 0.08
% 3.34/1.56  BG Simplification    : 0.02
% 3.34/1.56  Subsumption          : 0.08
% 3.34/1.56  Abstraction          : 0.02
% 3.34/1.56  MUC search           : 0.00
% 3.34/1.56  Cooper               : 0.00
% 3.34/1.56  Total                : 0.78
% 3.34/1.56  Index Insertion      : 0.00
% 3.34/1.56  Index Deletion       : 0.00
% 3.34/1.56  Index Matching       : 0.00
% 3.34/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
