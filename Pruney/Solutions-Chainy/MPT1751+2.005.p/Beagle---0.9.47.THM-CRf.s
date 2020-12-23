%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:58 EST 2020

% Result     : Theorem 29.54s
% Output     : CNFRefutation 29.54s
% Verified   : 
% Statistics : Number of formulae       :  204 (18433 expanded)
%              Number of leaves         :   46 (6847 expanded)
%              Depth                    :   42
%              Number of atoms          :  522 (99829 expanded)
%              Number of equality atoms :   48 (9844 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_185,negated_conjecture,(
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
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(B)))
                       => ( r1_tarski(E,u1_struct_0(C))
                         => k7_relset_1(u1_struct_0(B),u1_struct_0(A),D,E) = k7_relset_1(u1_struct_0(C),u1_struct_0(A),k2_tmap_1(B,A,D,C),E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tmap_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_131,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_135,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_149,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( ~ v1_xboole_0(D)
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,A,D)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,D))) )
         => ( ( r1_tarski(B,A)
              & r1_tarski(k7_relset_1(A,D,E,B),C) )
           => ( v1_funct_1(k2_partfun1(A,D,E,B))
              & v1_funct_2(k2_partfun1(A,D,E,B),B,C)
              & m1_subset_1(k2_partfun1(A,D,E,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_funct_2)).

tff(f_104,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(c_54,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_44,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_72,plain,(
    ! [C_89,A_90,B_91] :
      ( v1_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_76,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_72])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_60,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_58,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_66,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_64,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_50,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_441,plain,(
    ! [A_172,B_173,C_174,D_175] :
      ( k2_partfun1(A_172,B_173,C_174,D_175) = k7_relat_1(C_174,D_175)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_172,B_173)))
      | ~ v1_funct_1(C_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_443,plain,(
    ! [D_175] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_175) = k7_relat_1('#skF_4',D_175)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_441])).

tff(c_446,plain,(
    ! [D_175] : k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_175) = k7_relat_1('#skF_4',D_175) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_443])).

tff(c_1319,plain,(
    ! [A_293,B_294,C_295,D_296] :
      ( k2_partfun1(u1_struct_0(A_293),u1_struct_0(B_294),C_295,u1_struct_0(D_296)) = k2_tmap_1(A_293,B_294,C_295,D_296)
      | ~ m1_pre_topc(D_296,A_293)
      | ~ m1_subset_1(C_295,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_293),u1_struct_0(B_294))))
      | ~ v1_funct_2(C_295,u1_struct_0(A_293),u1_struct_0(B_294))
      | ~ v1_funct_1(C_295)
      | ~ l1_pre_topc(B_294)
      | ~ v2_pre_topc(B_294)
      | v2_struct_0(B_294)
      | ~ l1_pre_topc(A_293)
      | ~ v2_pre_topc(A_293)
      | v2_struct_0(A_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1324,plain,(
    ! [D_296] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_296)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_296)
      | ~ m1_pre_topc(D_296,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_48,c_1319])).

tff(c_1328,plain,(
    ! [D_296] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_296)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_296)
      | ~ m1_pre_topc(D_296,'#skF_2')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_66,c_64,c_52,c_50,c_446,c_1324])).

tff(c_1330,plain,(
    ! [D_297] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_297)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_297)
      | ~ m1_pre_topc(D_297,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_68,c_1328])).

tff(c_10,plain,(
    ! [A_8,C_12,B_11] :
      ( k9_relat_1(k7_relat_1(A_8,C_12),B_11) = k9_relat_1(A_8,B_11)
      | ~ r1_tarski(B_11,C_12)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1397,plain,(
    ! [D_297,B_11] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_297),B_11) = k9_relat_1('#skF_4',B_11)
      | ~ r1_tarski(B_11,u1_struct_0(D_297))
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc(D_297,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1330,c_10])).

tff(c_2145,plain,(
    ! [D_370,B_371] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_370),B_371) = k9_relat_1('#skF_4',B_371)
      | ~ r1_tarski(B_371,u1_struct_0(D_370))
      | ~ m1_pre_topc(D_370,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1397])).

tff(c_2198,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_2145])).

tff(c_2224,plain,(
    k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2198])).

tff(c_1329,plain,(
    ! [D_296] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_296)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_296)
      | ~ m1_pre_topc(D_296,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_68,c_1328])).

tff(c_36,plain,(
    ! [A_52] :
      ( m1_pre_topc(A_52,A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_586,plain,(
    ! [B_195,C_196,A_197] :
      ( r1_tarski(u1_struct_0(B_195),u1_struct_0(C_196))
      | ~ m1_pre_topc(B_195,C_196)
      | ~ m1_pre_topc(C_196,A_197)
      | ~ m1_pre_topc(B_195,A_197)
      | ~ l1_pre_topc(A_197)
      | ~ v2_pre_topc(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_602,plain,(
    ! [B_199,A_200] :
      ( r1_tarski(u1_struct_0(B_199),u1_struct_0(A_200))
      | ~ m1_pre_topc(B_199,A_200)
      | ~ v2_pre_topc(A_200)
      | ~ l1_pre_topc(A_200) ) ),
    inference(resolution,[status(thm)],[c_36,c_586])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_660,plain,(
    ! [A_205,A_206,B_207] :
      ( r1_tarski(A_205,u1_struct_0(A_206))
      | ~ r1_tarski(A_205,u1_struct_0(B_207))
      | ~ m1_pre_topc(B_207,A_206)
      | ~ v2_pre_topc(A_206)
      | ~ l1_pre_topc(A_206) ) ),
    inference(resolution,[status(thm)],[c_602,c_2])).

tff(c_699,plain,(
    ! [A_206] :
      ( r1_tarski('#skF_5',u1_struct_0(A_206))
      | ~ m1_pre_topc('#skF_3',A_206)
      | ~ v2_pre_topc(A_206)
      | ~ l1_pre_topc(A_206) ) ),
    inference(resolution,[status(thm)],[c_44,c_660])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( k2_relat_1(k7_relat_1(B_7,A_6)) = k9_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_124,plain,(
    ! [B_108,A_109] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_108,A_109)),k2_relat_1(B_108))
      | ~ v1_relat_1(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_132,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k9_relat_1(B_7,A_6),k2_relat_1(B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_124])).

tff(c_30,plain,(
    ! [A_35] :
      ( l1_struct_0(A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_324,plain,(
    ! [A_145,B_146,C_147,D_148] :
      ( k7_relset_1(A_145,B_146,C_147,D_148) = k9_relat_1(C_147,D_148)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_327,plain,(
    ! [D_148] : k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_148) = k9_relat_1('#skF_4',D_148) ),
    inference(resolution,[status(thm)],[c_48,c_324])).

tff(c_953,plain,(
    ! [A_246,B_245,C_248,D_244,E_247] :
      ( v1_funct_1(k2_partfun1(A_246,D_244,E_247,B_245))
      | ~ r1_tarski(k7_relset_1(A_246,D_244,E_247,B_245),C_248)
      | ~ r1_tarski(B_245,A_246)
      | ~ m1_subset_1(E_247,k1_zfmisc_1(k2_zfmisc_1(A_246,D_244)))
      | ~ v1_funct_2(E_247,A_246,D_244)
      | ~ v1_funct_1(E_247)
      | v1_xboole_0(D_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_958,plain,(
    ! [D_148,C_248] :
      ( v1_funct_1(k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_148))
      | ~ r1_tarski(k9_relat_1('#skF_4',D_148),C_248)
      | ~ r1_tarski(D_148,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_953])).

tff(c_964,plain,(
    ! [D_148,C_248] :
      ( v1_funct_1(k7_relat_1('#skF_4',D_148))
      | ~ r1_tarski(k9_relat_1('#skF_4',D_148),C_248)
      | ~ r1_tarski(D_148,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_446,c_958])).

tff(c_966,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_964])).

tff(c_32,plain,(
    ! [A_36] :
      ( ~ v1_xboole_0(u1_struct_0(A_36))
      | ~ l1_struct_0(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_969,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_966,c_32])).

tff(c_972,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_969])).

tff(c_975,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_972])).

tff(c_979,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_975])).

tff(c_992,plain,(
    ! [D_251,C_252] :
      ( v1_funct_1(k7_relat_1('#skF_4',D_251))
      | ~ r1_tarski(k9_relat_1('#skF_4',D_251),C_252)
      | ~ r1_tarski(D_251,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_964])).

tff(c_1012,plain,(
    ! [A_6] :
      ( v1_funct_1(k7_relat_1('#skF_4',A_6))
      | ~ r1_tarski(A_6,u1_struct_0('#skF_2'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_132,c_992])).

tff(c_1031,plain,(
    ! [A_253] :
      ( v1_funct_1(k7_relat_1('#skF_4',A_253))
      | ~ r1_tarski(A_253,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1012])).

tff(c_1043,plain,
    ( v1_funct_1(k7_relat_1('#skF_4','#skF_5'))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_699,c_1031])).

tff(c_1066,plain,(
    v1_funct_1(k7_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_60,c_54,c_1043])).

tff(c_591,plain,(
    ! [B_195,A_52] :
      ( r1_tarski(u1_struct_0(B_195),u1_struct_0(A_52))
      | ~ m1_pre_topc(B_195,A_52)
      | ~ v2_pre_topc(A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(resolution,[status(thm)],[c_36,c_586])).

tff(c_981,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_964])).

tff(c_1091,plain,(
    ! [A_268,B_267,C_270,D_266,E_269] :
      ( m1_subset_1(k2_partfun1(A_268,D_266,E_269,B_267),k1_zfmisc_1(k2_zfmisc_1(B_267,C_270)))
      | ~ r1_tarski(k7_relset_1(A_268,D_266,E_269,B_267),C_270)
      | ~ r1_tarski(B_267,A_268)
      | ~ m1_subset_1(E_269,k1_zfmisc_1(k2_zfmisc_1(A_268,D_266)))
      | ~ v1_funct_2(E_269,A_268,D_266)
      | ~ v1_funct_1(E_269)
      | v1_xboole_0(D_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_14,plain,(
    ! [C_17,A_15,B_16] :
      ( v1_relat_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1663,plain,(
    ! [A_308,D_307,E_306,C_310,B_309] :
      ( v1_relat_1(k2_partfun1(A_308,D_307,E_306,B_309))
      | ~ r1_tarski(k7_relset_1(A_308,D_307,E_306,B_309),C_310)
      | ~ r1_tarski(B_309,A_308)
      | ~ m1_subset_1(E_306,k1_zfmisc_1(k2_zfmisc_1(A_308,D_307)))
      | ~ v1_funct_2(E_306,A_308,D_307)
      | ~ v1_funct_1(E_306)
      | v1_xboole_0(D_307) ) ),
    inference(resolution,[status(thm)],[c_1091,c_14])).

tff(c_1668,plain,(
    ! [D_148,C_310] :
      ( v1_relat_1(k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_148))
      | ~ r1_tarski(k9_relat_1('#skF_4',D_148),C_310)
      | ~ r1_tarski(D_148,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_1663])).

tff(c_1674,plain,(
    ! [D_148,C_310] :
      ( v1_relat_1(k7_relat_1('#skF_4',D_148))
      | ~ r1_tarski(k9_relat_1('#skF_4',D_148),C_310)
      | ~ r1_tarski(D_148,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_446,c_1668])).

tff(c_1677,plain,(
    ! [D_311,C_312] :
      ( v1_relat_1(k7_relat_1('#skF_4',D_311))
      | ~ r1_tarski(k9_relat_1('#skF_4',D_311),C_312)
      | ~ r1_tarski(D_311,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_981,c_1674])).

tff(c_1700,plain,(
    ! [A_6] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_6))
      | ~ r1_tarski(A_6,u1_struct_0('#skF_2'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_132,c_1677])).

tff(c_1719,plain,(
    ! [A_313] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_313))
      | ~ r1_tarski(A_313,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1700])).

tff(c_1739,plain,(
    ! [B_195] :
      ( v1_relat_1(k7_relat_1('#skF_4',u1_struct_0(B_195)))
      | ~ m1_pre_topc(B_195,'#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_591,c_1719])).

tff(c_1762,plain,(
    ! [B_195] :
      ( v1_relat_1(k7_relat_1('#skF_4',u1_struct_0(B_195)))
      | ~ m1_pre_topc(B_195,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_60,c_1739])).

tff(c_243,plain,(
    ! [A_132,B_133,A_134] :
      ( r1_tarski(A_132,k2_relat_1(B_133))
      | ~ r1_tarski(A_132,k2_relat_1(k7_relat_1(B_133,A_134)))
      | ~ v1_relat_1(B_133) ) ),
    inference(resolution,[status(thm)],[c_124,c_2])).

tff(c_269,plain,(
    ! [B_133,A_134,A_6] :
      ( r1_tarski(k9_relat_1(k7_relat_1(B_133,A_134),A_6),k2_relat_1(B_133))
      | ~ v1_relat_1(B_133)
      | ~ v1_relat_1(k7_relat_1(B_133,A_134)) ) ),
    inference(resolution,[status(thm)],[c_132,c_243])).

tff(c_1385,plain,(
    ! [D_297,A_6] :
      ( r1_tarski(k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_297),A_6),k2_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_297)))
      | ~ m1_pre_topc(D_297,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1330,c_269])).

tff(c_3402,plain,(
    ! [D_460,A_461] :
      ( r1_tarski(k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_460),A_461),k2_relat_1('#skF_4'))
      | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_460)))
      | ~ m1_pre_topc(D_460,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1385])).

tff(c_3421,plain,
    ( r1_tarski(k9_relat_1('#skF_4','#skF_5'),k2_relat_1('#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2224,c_3402])).

tff(c_3434,plain,
    ( r1_tarski(k9_relat_1('#skF_4','#skF_5'),k2_relat_1('#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3421])).

tff(c_3435,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_3434])).

tff(c_3438,plain,(
    ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_1762,c_3435])).

tff(c_3448,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3438])).

tff(c_3449,plain,(
    r1_tarski(k9_relat_1('#skF_4','#skF_5'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3434])).

tff(c_22,plain,(
    ! [A_25,B_26,C_27,D_28] :
      ( k2_partfun1(A_25,B_26,C_27,D_28) = k7_relat_1(C_27,D_28)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2018,plain,(
    ! [C_356,B_355,E_351,D_352,A_354,D_353] :
      ( k2_partfun1(B_355,C_356,k2_partfun1(A_354,D_352,E_351,B_355),D_353) = k7_relat_1(k2_partfun1(A_354,D_352,E_351,B_355),D_353)
      | ~ v1_funct_1(k2_partfun1(A_354,D_352,E_351,B_355))
      | ~ r1_tarski(k7_relset_1(A_354,D_352,E_351,B_355),C_356)
      | ~ r1_tarski(B_355,A_354)
      | ~ m1_subset_1(E_351,k1_zfmisc_1(k2_zfmisc_1(A_354,D_352)))
      | ~ v1_funct_2(E_351,A_354,D_352)
      | ~ v1_funct_1(E_351)
      | v1_xboole_0(D_352) ) ),
    inference(resolution,[status(thm)],[c_1091,c_22])).

tff(c_2023,plain,(
    ! [D_148,C_356,D_353] :
      ( k2_partfun1(D_148,C_356,k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_148),D_353) = k7_relat_1(k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_148),D_353)
      | ~ v1_funct_1(k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_148))
      | ~ r1_tarski(k9_relat_1('#skF_4',D_148),C_356)
      | ~ r1_tarski(D_148,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_2018])).

tff(c_2029,plain,(
    ! [D_148,C_356,D_353] :
      ( k2_partfun1(D_148,C_356,k7_relat_1('#skF_4',D_148),D_353) = k7_relat_1(k7_relat_1('#skF_4',D_148),D_353)
      | ~ v1_funct_1(k7_relat_1('#skF_4',D_148))
      | ~ r1_tarski(k9_relat_1('#skF_4',D_148),C_356)
      | ~ r1_tarski(D_148,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_446,c_446,c_446,c_2023])).

tff(c_6783,plain,(
    ! [D_580,C_581,D_582] :
      ( k2_partfun1(D_580,C_581,k7_relat_1('#skF_4',D_580),D_582) = k7_relat_1(k7_relat_1('#skF_4',D_580),D_582)
      | ~ v1_funct_1(k7_relat_1('#skF_4',D_580))
      | ~ r1_tarski(k9_relat_1('#skF_4',D_580),C_581)
      | ~ r1_tarski(D_580,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_981,c_2029])).

tff(c_6805,plain,(
    ! [D_582] :
      ( k2_partfun1('#skF_5',k2_relat_1('#skF_4'),k7_relat_1('#skF_4','#skF_5'),D_582) = k7_relat_1(k7_relat_1('#skF_4','#skF_5'),D_582)
      | ~ v1_funct_1(k7_relat_1('#skF_4','#skF_5'))
      | ~ r1_tarski('#skF_5',u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_3449,c_6783])).

tff(c_6853,plain,(
    ! [D_582] :
      ( k2_partfun1('#skF_5',k2_relat_1('#skF_4'),k7_relat_1('#skF_4','#skF_5'),D_582) = k7_relat_1(k7_relat_1('#skF_4','#skF_5'),D_582)
      | ~ r1_tarski('#skF_5',u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1066,c_6805])).

tff(c_9906,plain,(
    ~ r1_tarski('#skF_5',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_6853])).

tff(c_9912,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_699,c_9906])).

tff(c_9919,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_60,c_54,c_9912])).

tff(c_9921,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_6853])).

tff(c_1448,plain,(
    ! [D_297,B_11] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_297),B_11) = k9_relat_1('#skF_4',B_11)
      | ~ r1_tarski(B_11,u1_struct_0(D_297))
      | ~ m1_pre_topc(D_297,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1397])).

tff(c_9949,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_2'),'#skF_5') = k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_9921,c_1448])).

tff(c_10638,plain,(
    ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_9949])).

tff(c_10641,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_10638])).

tff(c_10645,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_10641])).

tff(c_10647,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitRight,[status(thm)],[c_9949])).

tff(c_38,plain,(
    ! [B_57,C_59,A_53] :
      ( r1_tarski(u1_struct_0(B_57),u1_struct_0(C_59))
      | ~ m1_pre_topc(B_57,C_59)
      | ~ m1_pre_topc(C_59,A_53)
      | ~ m1_pre_topc(B_57,A_53)
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_10653,plain,(
    ! [B_57] :
      ( r1_tarski(u1_struct_0(B_57),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_57,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_10647,c_38])).

tff(c_10663,plain,(
    ! [B_761] :
      ( r1_tarski(u1_struct_0(B_761),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_761,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_10653])).

tff(c_608,plain,(
    ! [A_1,A_200,B_199] :
      ( r1_tarski(A_1,u1_struct_0(A_200))
      | ~ r1_tarski(A_1,u1_struct_0(B_199))
      | ~ m1_pre_topc(B_199,A_200)
      | ~ v2_pre_topc(A_200)
      | ~ l1_pre_topc(A_200) ) ),
    inference(resolution,[status(thm)],[c_602,c_2])).

tff(c_10701,plain,(
    ! [B_761,A_200] :
      ( r1_tarski(u1_struct_0(B_761),u1_struct_0(A_200))
      | ~ m1_pre_topc('#skF_2',A_200)
      | ~ v2_pre_topc(A_200)
      | ~ l1_pre_topc(A_200)
      | ~ m1_pre_topc(B_761,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_10663,c_608])).

tff(c_10672,plain,(
    ! [B_761] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_2'),u1_struct_0(B_761)) = k9_relat_1('#skF_4',u1_struct_0(B_761))
      | ~ m1_pre_topc('#skF_2','#skF_2')
      | ~ m1_pre_topc(B_761,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_10663,c_1448])).

tff(c_13537,plain,(
    ! [B_846] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_2'),u1_struct_0(B_846)) = k9_relat_1('#skF_4',u1_struct_0(B_846))
      | ~ m1_pre_topc(B_846,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10647,c_10672])).

tff(c_1440,plain,(
    ! [D_297,A_6] :
      ( r1_tarski(k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_297),A_6),k2_relat_1('#skF_4'))
      | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_297)))
      | ~ m1_pre_topc(D_297,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1385])).

tff(c_13602,plain,(
    ! [B_846] :
      ( r1_tarski(k9_relat_1('#skF_4',u1_struct_0(B_846)),k2_relat_1('#skF_4'))
      | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_2')))
      | ~ m1_pre_topc('#skF_2','#skF_2')
      | ~ m1_pre_topc(B_846,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13537,c_1440])).

tff(c_13655,plain,(
    ! [B_846] :
      ( r1_tarski(k9_relat_1('#skF_4',u1_struct_0(B_846)),k2_relat_1('#skF_4'))
      | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_846,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10647,c_13602])).

tff(c_13849,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_13655])).

tff(c_13852,plain,(
    ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_1762,c_13849])).

tff(c_13862,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10647,c_13852])).

tff(c_13864,plain,(
    v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_13655])).

tff(c_186,plain,(
    ! [A_123,C_124,B_125] :
      ( k9_relat_1(k7_relat_1(A_123,C_124),B_125) = k9_relat_1(A_123,B_125)
      | ~ r1_tarski(B_125,C_124)
      | ~ v1_relat_1(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_3904,plain,(
    ! [A_474,B_475,C_476] :
      ( r1_tarski(k9_relat_1(A_474,B_475),k2_relat_1(k7_relat_1(A_474,C_476)))
      | ~ v1_relat_1(k7_relat_1(A_474,C_476))
      | ~ v1_relat_1(k7_relat_1(A_474,C_476))
      | ~ r1_tarski(B_475,C_476)
      | ~ v1_relat_1(A_474) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_132])).

tff(c_3958,plain,(
    ! [B_7,B_475,A_6] :
      ( r1_tarski(k9_relat_1(B_7,B_475),k9_relat_1(B_7,A_6))
      | ~ v1_relat_1(k7_relat_1(B_7,A_6))
      | ~ v1_relat_1(k7_relat_1(B_7,A_6))
      | ~ r1_tarski(B_475,A_6)
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_3904])).

tff(c_4,plain,(
    ! [B_5,A_4] :
      ( v5_relat_1(B_5,A_4)
      | ~ r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_136,plain,(
    ! [B_108,A_109] :
      ( v5_relat_1(k7_relat_1(B_108,A_109),k2_relat_1(B_108))
      | ~ v1_relat_1(k7_relat_1(B_108,A_109))
      | ~ v1_relat_1(B_108) ) ),
    inference(resolution,[status(thm)],[c_124,c_4])).

tff(c_108,plain,(
    ! [C_103,B_104,A_105] :
      ( v5_relat_1(C_103,B_104)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_105,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_112,plain,(
    v5_relat_1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_48,c_108])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_113,plain,(
    ! [B_106,A_107] :
      ( r1_tarski(k2_relat_1(B_106),A_107)
      | ~ v5_relat_1(B_106,A_107)
      | ~ v1_relat_1(B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_173,plain,(
    ! [A_120,A_121,B_122] :
      ( r1_tarski(A_120,A_121)
      | ~ r1_tarski(A_120,k2_relat_1(B_122))
      | ~ v5_relat_1(B_122,A_121)
      | ~ v1_relat_1(B_122) ) ),
    inference(resolution,[status(thm)],[c_113,c_2])).

tff(c_426,plain,(
    ! [B_169,A_170,B_171] :
      ( r1_tarski(k2_relat_1(B_169),A_170)
      | ~ v5_relat_1(B_171,A_170)
      | ~ v1_relat_1(B_171)
      | ~ v5_relat_1(B_169,k2_relat_1(B_171))
      | ~ v1_relat_1(B_169) ) ),
    inference(resolution,[status(thm)],[c_6,c_173])).

tff(c_434,plain,(
    ! [B_169] :
      ( r1_tarski(k2_relat_1(B_169),u1_struct_0('#skF_1'))
      | ~ v1_relat_1('#skF_4')
      | ~ v5_relat_1(B_169,k2_relat_1('#skF_4'))
      | ~ v1_relat_1(B_169) ) ),
    inference(resolution,[status(thm)],[c_112,c_426])).

tff(c_456,plain,(
    ! [B_177] :
      ( r1_tarski(k2_relat_1(B_177),u1_struct_0('#skF_1'))
      | ~ v5_relat_1(B_177,k2_relat_1('#skF_4'))
      | ~ v1_relat_1(B_177) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_434])).

tff(c_468,plain,(
    ! [B_177] :
      ( v5_relat_1(B_177,u1_struct_0('#skF_1'))
      | ~ v5_relat_1(B_177,k2_relat_1('#skF_4'))
      | ~ v1_relat_1(B_177) ) ),
    inference(resolution,[status(thm)],[c_456,c_4])).

tff(c_10696,plain,(
    ! [B_761] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_2'),u1_struct_0(B_761)) = k9_relat_1('#skF_4',u1_struct_0(B_761))
      | ~ m1_pre_topc(B_761,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10647,c_10672])).

tff(c_778,plain,(
    ! [B_220,A_221,A_222] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(B_220,A_221),A_222)),k9_relat_1(B_220,A_221))
      | ~ v1_relat_1(k7_relat_1(B_220,A_221))
      | ~ v1_relat_1(B_220) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_124])).

tff(c_2785,plain,(
    ! [B_406,A_407,A_408] :
      ( r1_tarski(k9_relat_1(k7_relat_1(B_406,A_407),A_408),k9_relat_1(B_406,A_407))
      | ~ v1_relat_1(k7_relat_1(B_406,A_407))
      | ~ v1_relat_1(B_406)
      | ~ v1_relat_1(k7_relat_1(B_406,A_407)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_778])).

tff(c_2819,plain,(
    ! [D_296,A_408] :
      ( r1_tarski(k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_296),A_408),k9_relat_1('#skF_4',u1_struct_0(D_296)))
      | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_296)))
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_296)))
      | ~ m1_pre_topc(D_296,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1329,c_2785])).

tff(c_21193,plain,(
    ! [D_1087,A_1088] :
      ( r1_tarski(k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_1087),A_1088),k9_relat_1('#skF_4',u1_struct_0(D_1087)))
      | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_1087)))
      | ~ m1_pre_topc(D_1087,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2819])).

tff(c_21254,plain,(
    ! [B_761] :
      ( r1_tarski(k9_relat_1('#skF_4',u1_struct_0(B_761)),k9_relat_1('#skF_4',u1_struct_0('#skF_2')))
      | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_2')))
      | ~ m1_pre_topc('#skF_2','#skF_2')
      | ~ m1_pre_topc(B_761,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10696,c_21193])).

tff(c_23145,plain,(
    ! [B_1100] :
      ( r1_tarski(k9_relat_1('#skF_4',u1_struct_0(B_1100)),k9_relat_1('#skF_4',u1_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_1100,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10647,c_13864,c_21254])).

tff(c_182,plain,(
    ! [A_120,A_121,B_7,A_6] :
      ( r1_tarski(A_120,A_121)
      | ~ r1_tarski(A_120,k9_relat_1(B_7,A_6))
      | ~ v5_relat_1(k7_relat_1(B_7,A_6),A_121)
      | ~ v1_relat_1(k7_relat_1(B_7,A_6))
      | ~ v1_relat_1(B_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_173])).

tff(c_23200,plain,(
    ! [B_1100,A_121] :
      ( r1_tarski(k9_relat_1('#skF_4',u1_struct_0(B_1100)),A_121)
      | ~ v5_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_2')),A_121)
      | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_2')))
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc(B_1100,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_23145,c_182])).

tff(c_30324,plain,(
    ! [B_1182,A_1183] :
      ( r1_tarski(k9_relat_1('#skF_4',u1_struct_0(B_1182)),A_1183)
      | ~ v5_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_2')),A_1183)
      | ~ m1_pre_topc(B_1182,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_13864,c_23200])).

tff(c_30375,plain,(
    ! [B_1182] :
      ( r1_tarski(k9_relat_1('#skF_4',u1_struct_0(B_1182)),u1_struct_0('#skF_1'))
      | ~ m1_pre_topc(B_1182,'#skF_2')
      | ~ v5_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_2')),k2_relat_1('#skF_4'))
      | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_468,c_30324])).

tff(c_30432,plain,(
    ! [B_1182] :
      ( r1_tarski(k9_relat_1('#skF_4',u1_struct_0(B_1182)),u1_struct_0('#skF_1'))
      | ~ m1_pre_topc(B_1182,'#skF_2')
      | ~ v5_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_2')),k2_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13864,c_30375])).

tff(c_44696,plain,(
    ~ v5_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_2')),k2_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_30432])).

tff(c_44714,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_2')))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_136,c_44696])).

tff(c_44730,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_13864,c_44714])).

tff(c_44732,plain,(
    v5_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_2')),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_30432])).

tff(c_75274,plain,(
    ! [B_1803,A_1804] :
      ( r1_tarski(k9_relat_1(B_1803,A_1804),u1_struct_0('#skF_1'))
      | ~ v5_relat_1(k7_relat_1(B_1803,A_1804),k2_relat_1('#skF_4'))
      | ~ v1_relat_1(k7_relat_1(B_1803,A_1804))
      | ~ v1_relat_1(B_1803) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_456])).

tff(c_75283,plain,
    ( r1_tarski(k9_relat_1('#skF_4',u1_struct_0('#skF_2')),u1_struct_0('#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_2')))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44732,c_75274])).

tff(c_75332,plain,(
    r1_tarski(k9_relat_1('#skF_4',u1_struct_0('#skF_2')),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_13864,c_75283])).

tff(c_75961,plain,(
    ! [A_1809] :
      ( r1_tarski(A_1809,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_1809,k9_relat_1('#skF_4',u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_75332,c_2])).

tff(c_76074,plain,(
    ! [B_475] :
      ( r1_tarski(k9_relat_1('#skF_4',B_475),u1_struct_0('#skF_1'))
      | ~ v1_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_2')))
      | ~ r1_tarski(B_475,u1_struct_0('#skF_2'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3958,c_75961])).

tff(c_76749,plain,(
    ! [B_1815] :
      ( r1_tarski(k9_relat_1('#skF_4',B_1815),u1_struct_0('#skF_1'))
      | ~ r1_tarski(B_1815,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_13864,c_76074])).

tff(c_20,plain,(
    ! [A_21,B_22,C_23,D_24] :
      ( k7_relset_1(A_21,B_22,C_23,D_24) = k9_relat_1(C_23,D_24)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1942,plain,(
    ! [B_346,E_342,D_343,D_344,A_345,C_347] :
      ( k7_relset_1(B_346,C_347,k2_partfun1(A_345,D_343,E_342,B_346),D_344) = k9_relat_1(k2_partfun1(A_345,D_343,E_342,B_346),D_344)
      | ~ r1_tarski(k7_relset_1(A_345,D_343,E_342,B_346),C_347)
      | ~ r1_tarski(B_346,A_345)
      | ~ m1_subset_1(E_342,k1_zfmisc_1(k2_zfmisc_1(A_345,D_343)))
      | ~ v1_funct_2(E_342,A_345,D_343)
      | ~ v1_funct_1(E_342)
      | v1_xboole_0(D_343) ) ),
    inference(resolution,[status(thm)],[c_1091,c_20])).

tff(c_1947,plain,(
    ! [D_148,C_347,D_344] :
      ( k7_relset_1(D_148,C_347,k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_148),D_344) = k9_relat_1(k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_148),D_344)
      | ~ r1_tarski(k9_relat_1('#skF_4',D_148),C_347)
      | ~ r1_tarski(D_148,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_1942])).

tff(c_1953,plain,(
    ! [D_148,C_347,D_344] :
      ( k7_relset_1(D_148,C_347,k7_relat_1('#skF_4',D_148),D_344) = k9_relat_1(k7_relat_1('#skF_4',D_148),D_344)
      | ~ r1_tarski(k9_relat_1('#skF_4',D_148),C_347)
      | ~ r1_tarski(D_148,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_446,c_446,c_1947])).

tff(c_1954,plain,(
    ! [D_148,C_347,D_344] :
      ( k7_relset_1(D_148,C_347,k7_relat_1('#skF_4',D_148),D_344) = k9_relat_1(k7_relat_1('#skF_4',D_148),D_344)
      | ~ r1_tarski(k9_relat_1('#skF_4',D_148),C_347)
      | ~ r1_tarski(D_148,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_981,c_1953])).

tff(c_90438,plain,(
    ! [B_1977,D_1978] :
      ( k7_relset_1(B_1977,u1_struct_0('#skF_1'),k7_relat_1('#skF_4',B_1977),D_1978) = k9_relat_1(k7_relat_1('#skF_4',B_1977),D_1978)
      | ~ r1_tarski(B_1977,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_76749,c_1954])).

tff(c_90725,plain,(
    ! [D_1983,D_1984] :
      ( k7_relset_1(u1_struct_0(D_1983),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4',D_1983),D_1984) = k9_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_1983)),D_1984)
      | ~ r1_tarski(u1_struct_0(D_1983),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_1983,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1329,c_90438])).

tff(c_42,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_328,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_42])).

tff(c_90741,plain,
    ( k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90725,c_328])).

tff(c_90752,plain,
    ( k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_90741])).

tff(c_90754,plain,(
    ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_90752])).

tff(c_90757,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_10701,c_90754])).

tff(c_90779,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_58,c_60,c_10647,c_90757])).

tff(c_90780,plain,(
    k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_90752])).

tff(c_92481,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1329,c_90780])).

tff(c_92487,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2224,c_92481])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:43:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 29.54/20.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.54/20.58  
% 29.54/20.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.54/20.58  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 29.54/20.58  
% 29.54/20.58  %Foreground sorts:
% 29.54/20.58  
% 29.54/20.58  
% 29.54/20.58  %Background operators:
% 29.54/20.58  
% 29.54/20.58  
% 29.54/20.58  %Foreground operators:
% 29.54/20.58  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 29.54/20.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 29.54/20.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 29.54/20.58  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 29.54/20.58  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 29.54/20.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 29.54/20.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 29.54/20.58  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 29.54/20.58  tff('#skF_5', type, '#skF_5': $i).
% 29.54/20.58  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 29.54/20.58  tff('#skF_2', type, '#skF_2': $i).
% 29.54/20.58  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 29.54/20.58  tff('#skF_3', type, '#skF_3': $i).
% 29.54/20.58  tff('#skF_1', type, '#skF_1': $i).
% 29.54/20.58  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 29.54/20.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 29.54/20.58  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 29.54/20.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 29.54/20.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 29.54/20.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 29.54/20.58  tff('#skF_4', type, '#skF_4': $i).
% 29.54/20.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 29.54/20.58  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 29.54/20.58  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 29.54/20.58  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 29.54/20.58  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 29.54/20.58  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 29.54/20.58  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 29.54/20.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 29.54/20.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 29.54/20.58  
% 29.54/20.61  tff(f_185, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (r1_tarski(E, u1_struct_0(C)) => (k7_relset_1(u1_struct_0(B), u1_struct_0(A), D, E) = k7_relset_1(u1_struct_0(C), u1_struct_0(A), k2_tmap_1(B, A, D, C), E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_tmap_1)).
% 29.54/20.61  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 29.54/20.61  tff(f_72, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 29.54/20.61  tff(f_131, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 29.54/20.61  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 29.54/20.61  tff(f_135, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 29.54/20.61  tff(f_149, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 29.54/20.61  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 29.54/20.61  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 29.54/20.61  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k7_relat_1(B, A)), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_relat_1)).
% 29.54/20.61  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 29.54/20.61  tff(f_66, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 29.54/20.61  tff(f_92, axiom, (![A, B, C, D]: (~v1_xboole_0(D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, A, D)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, D)))) => ((r1_tarski(B, A) & r1_tarski(k7_relset_1(A, D, E, B), C)) => ((v1_funct_1(k2_partfun1(A, D, E, B)) & v1_funct_2(k2_partfun1(A, D, E, B), B, C)) & m1_subset_1(k2_partfun1(A, D, E, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_funct_2)).
% 29.54/20.61  tff(f_104, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 29.54/20.61  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 29.54/20.61  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 29.54/20.61  tff(c_54, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_185])).
% 29.54/20.61  tff(c_44, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_185])).
% 29.54/20.61  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_185])).
% 29.54/20.61  tff(c_72, plain, (![C_89, A_90, B_91]: (v1_relat_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 29.54/20.61  tff(c_76, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_72])).
% 29.54/20.61  tff(c_62, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_185])).
% 29.54/20.61  tff(c_68, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_185])).
% 29.54/20.61  tff(c_60, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_185])).
% 29.54/20.61  tff(c_58, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_185])).
% 29.54/20.61  tff(c_66, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_185])).
% 29.54/20.61  tff(c_64, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_185])).
% 29.54/20.61  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_185])).
% 29.54/20.61  tff(c_50, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_185])).
% 29.54/20.61  tff(c_441, plain, (![A_172, B_173, C_174, D_175]: (k2_partfun1(A_172, B_173, C_174, D_175)=k7_relat_1(C_174, D_175) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_172, B_173))) | ~v1_funct_1(C_174))), inference(cnfTransformation, [status(thm)], [f_72])).
% 29.54/20.61  tff(c_443, plain, (![D_175]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_175)=k7_relat_1('#skF_4', D_175) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_441])).
% 29.54/20.61  tff(c_446, plain, (![D_175]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_175)=k7_relat_1('#skF_4', D_175))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_443])).
% 29.54/20.61  tff(c_1319, plain, (![A_293, B_294, C_295, D_296]: (k2_partfun1(u1_struct_0(A_293), u1_struct_0(B_294), C_295, u1_struct_0(D_296))=k2_tmap_1(A_293, B_294, C_295, D_296) | ~m1_pre_topc(D_296, A_293) | ~m1_subset_1(C_295, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_293), u1_struct_0(B_294)))) | ~v1_funct_2(C_295, u1_struct_0(A_293), u1_struct_0(B_294)) | ~v1_funct_1(C_295) | ~l1_pre_topc(B_294) | ~v2_pre_topc(B_294) | v2_struct_0(B_294) | ~l1_pre_topc(A_293) | ~v2_pre_topc(A_293) | v2_struct_0(A_293))), inference(cnfTransformation, [status(thm)], [f_131])).
% 29.54/20.61  tff(c_1324, plain, (![D_296]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_296))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_296) | ~m1_pre_topc(D_296, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_1319])).
% 29.54/20.61  tff(c_1328, plain, (![D_296]: (k7_relat_1('#skF_4', u1_struct_0(D_296))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_296) | ~m1_pre_topc(D_296, '#skF_2') | v2_struct_0('#skF_1') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_66, c_64, c_52, c_50, c_446, c_1324])).
% 29.54/20.61  tff(c_1330, plain, (![D_297]: (k7_relat_1('#skF_4', u1_struct_0(D_297))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_297) | ~m1_pre_topc(D_297, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_62, c_68, c_1328])).
% 29.54/20.61  tff(c_10, plain, (![A_8, C_12, B_11]: (k9_relat_1(k7_relat_1(A_8, C_12), B_11)=k9_relat_1(A_8, B_11) | ~r1_tarski(B_11, C_12) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 29.54/20.61  tff(c_1397, plain, (![D_297, B_11]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_297), B_11)=k9_relat_1('#skF_4', B_11) | ~r1_tarski(B_11, u1_struct_0(D_297)) | ~v1_relat_1('#skF_4') | ~m1_pre_topc(D_297, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1330, c_10])).
% 29.54/20.61  tff(c_2145, plain, (![D_370, B_371]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_370), B_371)=k9_relat_1('#skF_4', B_371) | ~r1_tarski(B_371, u1_struct_0(D_370)) | ~m1_pre_topc(D_370, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1397])).
% 29.54/20.61  tff(c_2198, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_2145])).
% 29.54/20.61  tff(c_2224, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2198])).
% 29.54/20.61  tff(c_1329, plain, (![D_296]: (k7_relat_1('#skF_4', u1_struct_0(D_296))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_296) | ~m1_pre_topc(D_296, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_62, c_68, c_1328])).
% 29.54/20.61  tff(c_36, plain, (![A_52]: (m1_pre_topc(A_52, A_52) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_135])).
% 29.54/20.61  tff(c_586, plain, (![B_195, C_196, A_197]: (r1_tarski(u1_struct_0(B_195), u1_struct_0(C_196)) | ~m1_pre_topc(B_195, C_196) | ~m1_pre_topc(C_196, A_197) | ~m1_pre_topc(B_195, A_197) | ~l1_pre_topc(A_197) | ~v2_pre_topc(A_197))), inference(cnfTransformation, [status(thm)], [f_149])).
% 29.54/20.61  tff(c_602, plain, (![B_199, A_200]: (r1_tarski(u1_struct_0(B_199), u1_struct_0(A_200)) | ~m1_pre_topc(B_199, A_200) | ~v2_pre_topc(A_200) | ~l1_pre_topc(A_200))), inference(resolution, [status(thm)], [c_36, c_586])).
% 29.54/20.61  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 29.54/20.61  tff(c_660, plain, (![A_205, A_206, B_207]: (r1_tarski(A_205, u1_struct_0(A_206)) | ~r1_tarski(A_205, u1_struct_0(B_207)) | ~m1_pre_topc(B_207, A_206) | ~v2_pre_topc(A_206) | ~l1_pre_topc(A_206))), inference(resolution, [status(thm)], [c_602, c_2])).
% 29.54/20.61  tff(c_699, plain, (![A_206]: (r1_tarski('#skF_5', u1_struct_0(A_206)) | ~m1_pre_topc('#skF_3', A_206) | ~v2_pre_topc(A_206) | ~l1_pre_topc(A_206))), inference(resolution, [status(thm)], [c_44, c_660])).
% 29.54/20.61  tff(c_8, plain, (![B_7, A_6]: (k2_relat_1(k7_relat_1(B_7, A_6))=k9_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 29.54/20.61  tff(c_124, plain, (![B_108, A_109]: (r1_tarski(k2_relat_1(k7_relat_1(B_108, A_109)), k2_relat_1(B_108)) | ~v1_relat_1(B_108))), inference(cnfTransformation, [status(thm)], [f_52])).
% 29.54/20.61  tff(c_132, plain, (![B_7, A_6]: (r1_tarski(k9_relat_1(B_7, A_6), k2_relat_1(B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(B_7))), inference(superposition, [status(thm), theory('equality')], [c_8, c_124])).
% 29.54/20.61  tff(c_30, plain, (![A_35]: (l1_struct_0(A_35) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_96])).
% 29.54/20.61  tff(c_324, plain, (![A_145, B_146, C_147, D_148]: (k7_relset_1(A_145, B_146, C_147, D_148)=k9_relat_1(C_147, D_148) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 29.54/20.61  tff(c_327, plain, (![D_148]: (k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_148)=k9_relat_1('#skF_4', D_148))), inference(resolution, [status(thm)], [c_48, c_324])).
% 29.54/20.61  tff(c_953, plain, (![A_246, B_245, C_248, D_244, E_247]: (v1_funct_1(k2_partfun1(A_246, D_244, E_247, B_245)) | ~r1_tarski(k7_relset_1(A_246, D_244, E_247, B_245), C_248) | ~r1_tarski(B_245, A_246) | ~m1_subset_1(E_247, k1_zfmisc_1(k2_zfmisc_1(A_246, D_244))) | ~v1_funct_2(E_247, A_246, D_244) | ~v1_funct_1(E_247) | v1_xboole_0(D_244))), inference(cnfTransformation, [status(thm)], [f_92])).
% 29.54/20.61  tff(c_958, plain, (![D_148, C_248]: (v1_funct_1(k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_148)) | ~r1_tarski(k9_relat_1('#skF_4', D_148), C_248) | ~r1_tarski(D_148, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_327, c_953])).
% 29.54/20.61  tff(c_964, plain, (![D_148, C_248]: (v1_funct_1(k7_relat_1('#skF_4', D_148)) | ~r1_tarski(k9_relat_1('#skF_4', D_148), C_248) | ~r1_tarski(D_148, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_446, c_958])).
% 29.54/20.61  tff(c_966, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_964])).
% 29.54/20.61  tff(c_32, plain, (![A_36]: (~v1_xboole_0(u1_struct_0(A_36)) | ~l1_struct_0(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_104])).
% 29.54/20.61  tff(c_969, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_966, c_32])).
% 29.54/20.61  tff(c_972, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_68, c_969])).
% 29.54/20.61  tff(c_975, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_972])).
% 29.54/20.61  tff(c_979, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_975])).
% 29.54/20.61  tff(c_992, plain, (![D_251, C_252]: (v1_funct_1(k7_relat_1('#skF_4', D_251)) | ~r1_tarski(k9_relat_1('#skF_4', D_251), C_252) | ~r1_tarski(D_251, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_964])).
% 29.54/20.61  tff(c_1012, plain, (![A_6]: (v1_funct_1(k7_relat_1('#skF_4', A_6)) | ~r1_tarski(A_6, u1_struct_0('#skF_2')) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_132, c_992])).
% 29.54/20.61  tff(c_1031, plain, (![A_253]: (v1_funct_1(k7_relat_1('#skF_4', A_253)) | ~r1_tarski(A_253, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1012])).
% 29.54/20.61  tff(c_1043, plain, (v1_funct_1(k7_relat_1('#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_3', '#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_699, c_1031])).
% 29.54/20.61  tff(c_1066, plain, (v1_funct_1(k7_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_60, c_54, c_1043])).
% 29.54/20.61  tff(c_591, plain, (![B_195, A_52]: (r1_tarski(u1_struct_0(B_195), u1_struct_0(A_52)) | ~m1_pre_topc(B_195, A_52) | ~v2_pre_topc(A_52) | ~l1_pre_topc(A_52))), inference(resolution, [status(thm)], [c_36, c_586])).
% 29.54/20.61  tff(c_981, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_964])).
% 29.54/20.61  tff(c_1091, plain, (![A_268, B_267, C_270, D_266, E_269]: (m1_subset_1(k2_partfun1(A_268, D_266, E_269, B_267), k1_zfmisc_1(k2_zfmisc_1(B_267, C_270))) | ~r1_tarski(k7_relset_1(A_268, D_266, E_269, B_267), C_270) | ~r1_tarski(B_267, A_268) | ~m1_subset_1(E_269, k1_zfmisc_1(k2_zfmisc_1(A_268, D_266))) | ~v1_funct_2(E_269, A_268, D_266) | ~v1_funct_1(E_269) | v1_xboole_0(D_266))), inference(cnfTransformation, [status(thm)], [f_92])).
% 29.54/20.61  tff(c_14, plain, (![C_17, A_15, B_16]: (v1_relat_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 29.54/20.61  tff(c_1663, plain, (![A_308, D_307, E_306, C_310, B_309]: (v1_relat_1(k2_partfun1(A_308, D_307, E_306, B_309)) | ~r1_tarski(k7_relset_1(A_308, D_307, E_306, B_309), C_310) | ~r1_tarski(B_309, A_308) | ~m1_subset_1(E_306, k1_zfmisc_1(k2_zfmisc_1(A_308, D_307))) | ~v1_funct_2(E_306, A_308, D_307) | ~v1_funct_1(E_306) | v1_xboole_0(D_307))), inference(resolution, [status(thm)], [c_1091, c_14])).
% 29.54/20.61  tff(c_1668, plain, (![D_148, C_310]: (v1_relat_1(k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_148)) | ~r1_tarski(k9_relat_1('#skF_4', D_148), C_310) | ~r1_tarski(D_148, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_327, c_1663])).
% 29.54/20.61  tff(c_1674, plain, (![D_148, C_310]: (v1_relat_1(k7_relat_1('#skF_4', D_148)) | ~r1_tarski(k9_relat_1('#skF_4', D_148), C_310) | ~r1_tarski(D_148, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_446, c_1668])).
% 29.54/20.61  tff(c_1677, plain, (![D_311, C_312]: (v1_relat_1(k7_relat_1('#skF_4', D_311)) | ~r1_tarski(k9_relat_1('#skF_4', D_311), C_312) | ~r1_tarski(D_311, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_981, c_1674])).
% 29.54/20.61  tff(c_1700, plain, (![A_6]: (v1_relat_1(k7_relat_1('#skF_4', A_6)) | ~r1_tarski(A_6, u1_struct_0('#skF_2')) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_132, c_1677])).
% 29.54/20.61  tff(c_1719, plain, (![A_313]: (v1_relat_1(k7_relat_1('#skF_4', A_313)) | ~r1_tarski(A_313, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1700])).
% 29.54/20.61  tff(c_1739, plain, (![B_195]: (v1_relat_1(k7_relat_1('#skF_4', u1_struct_0(B_195))) | ~m1_pre_topc(B_195, '#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_591, c_1719])).
% 29.54/20.61  tff(c_1762, plain, (![B_195]: (v1_relat_1(k7_relat_1('#skF_4', u1_struct_0(B_195))) | ~m1_pre_topc(B_195, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_60, c_1739])).
% 29.54/20.61  tff(c_243, plain, (![A_132, B_133, A_134]: (r1_tarski(A_132, k2_relat_1(B_133)) | ~r1_tarski(A_132, k2_relat_1(k7_relat_1(B_133, A_134))) | ~v1_relat_1(B_133))), inference(resolution, [status(thm)], [c_124, c_2])).
% 29.54/20.61  tff(c_269, plain, (![B_133, A_134, A_6]: (r1_tarski(k9_relat_1(k7_relat_1(B_133, A_134), A_6), k2_relat_1(B_133)) | ~v1_relat_1(B_133) | ~v1_relat_1(k7_relat_1(B_133, A_134)))), inference(resolution, [status(thm)], [c_132, c_243])).
% 29.54/20.61  tff(c_1385, plain, (![D_297, A_6]: (r1_tarski(k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_297), A_6), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_297))) | ~m1_pre_topc(D_297, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1330, c_269])).
% 29.54/20.61  tff(c_3402, plain, (![D_460, A_461]: (r1_tarski(k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_460), A_461), k2_relat_1('#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_460))) | ~m1_pre_topc(D_460, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1385])).
% 29.54/20.61  tff(c_3421, plain, (r1_tarski(k9_relat_1('#skF_4', '#skF_5'), k2_relat_1('#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2224, c_3402])).
% 29.54/20.61  tff(c_3434, plain, (r1_tarski(k9_relat_1('#skF_4', '#skF_5'), k2_relat_1('#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3421])).
% 29.54/20.61  tff(c_3435, plain, (~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_3434])).
% 29.54/20.61  tff(c_3438, plain, (~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_1762, c_3435])).
% 29.54/20.61  tff(c_3448, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_3438])).
% 29.54/20.61  tff(c_3449, plain, (r1_tarski(k9_relat_1('#skF_4', '#skF_5'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_3434])).
% 29.54/20.61  tff(c_22, plain, (![A_25, B_26, C_27, D_28]: (k2_partfun1(A_25, B_26, C_27, D_28)=k7_relat_1(C_27, D_28) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_1(C_27))), inference(cnfTransformation, [status(thm)], [f_72])).
% 29.54/20.61  tff(c_2018, plain, (![C_356, B_355, E_351, D_352, A_354, D_353]: (k2_partfun1(B_355, C_356, k2_partfun1(A_354, D_352, E_351, B_355), D_353)=k7_relat_1(k2_partfun1(A_354, D_352, E_351, B_355), D_353) | ~v1_funct_1(k2_partfun1(A_354, D_352, E_351, B_355)) | ~r1_tarski(k7_relset_1(A_354, D_352, E_351, B_355), C_356) | ~r1_tarski(B_355, A_354) | ~m1_subset_1(E_351, k1_zfmisc_1(k2_zfmisc_1(A_354, D_352))) | ~v1_funct_2(E_351, A_354, D_352) | ~v1_funct_1(E_351) | v1_xboole_0(D_352))), inference(resolution, [status(thm)], [c_1091, c_22])).
% 29.54/20.61  tff(c_2023, plain, (![D_148, C_356, D_353]: (k2_partfun1(D_148, C_356, k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_148), D_353)=k7_relat_1(k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_148), D_353) | ~v1_funct_1(k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_148)) | ~r1_tarski(k9_relat_1('#skF_4', D_148), C_356) | ~r1_tarski(D_148, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_327, c_2018])).
% 29.54/20.61  tff(c_2029, plain, (![D_148, C_356, D_353]: (k2_partfun1(D_148, C_356, k7_relat_1('#skF_4', D_148), D_353)=k7_relat_1(k7_relat_1('#skF_4', D_148), D_353) | ~v1_funct_1(k7_relat_1('#skF_4', D_148)) | ~r1_tarski(k9_relat_1('#skF_4', D_148), C_356) | ~r1_tarski(D_148, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_446, c_446, c_446, c_2023])).
% 29.54/20.61  tff(c_6783, plain, (![D_580, C_581, D_582]: (k2_partfun1(D_580, C_581, k7_relat_1('#skF_4', D_580), D_582)=k7_relat_1(k7_relat_1('#skF_4', D_580), D_582) | ~v1_funct_1(k7_relat_1('#skF_4', D_580)) | ~r1_tarski(k9_relat_1('#skF_4', D_580), C_581) | ~r1_tarski(D_580, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_981, c_2029])).
% 29.54/20.61  tff(c_6805, plain, (![D_582]: (k2_partfun1('#skF_5', k2_relat_1('#skF_4'), k7_relat_1('#skF_4', '#skF_5'), D_582)=k7_relat_1(k7_relat_1('#skF_4', '#skF_5'), D_582) | ~v1_funct_1(k7_relat_1('#skF_4', '#skF_5')) | ~r1_tarski('#skF_5', u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_3449, c_6783])).
% 29.54/20.61  tff(c_6853, plain, (![D_582]: (k2_partfun1('#skF_5', k2_relat_1('#skF_4'), k7_relat_1('#skF_4', '#skF_5'), D_582)=k7_relat_1(k7_relat_1('#skF_4', '#skF_5'), D_582) | ~r1_tarski('#skF_5', u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1066, c_6805])).
% 29.54/20.61  tff(c_9906, plain, (~r1_tarski('#skF_5', u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_6853])).
% 29.54/20.61  tff(c_9912, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_699, c_9906])).
% 29.54/20.61  tff(c_9919, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_60, c_54, c_9912])).
% 29.54/20.61  tff(c_9921, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_6853])).
% 29.54/20.61  tff(c_1448, plain, (![D_297, B_11]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_297), B_11)=k9_relat_1('#skF_4', B_11) | ~r1_tarski(B_11, u1_struct_0(D_297)) | ~m1_pre_topc(D_297, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1397])).
% 29.54/20.61  tff(c_9949, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_2'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_9921, c_1448])).
% 29.54/20.61  tff(c_10638, plain, (~m1_pre_topc('#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_9949])).
% 29.54/20.61  tff(c_10641, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_36, c_10638])).
% 29.54/20.61  tff(c_10645, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_10641])).
% 29.54/20.61  tff(c_10647, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(splitRight, [status(thm)], [c_9949])).
% 29.54/20.61  tff(c_38, plain, (![B_57, C_59, A_53]: (r1_tarski(u1_struct_0(B_57), u1_struct_0(C_59)) | ~m1_pre_topc(B_57, C_59) | ~m1_pre_topc(C_59, A_53) | ~m1_pre_topc(B_57, A_53) | ~l1_pre_topc(A_53) | ~v2_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_149])).
% 29.54/20.61  tff(c_10653, plain, (![B_57]: (r1_tarski(u1_struct_0(B_57), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_57, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_10647, c_38])).
% 29.54/20.61  tff(c_10663, plain, (![B_761]: (r1_tarski(u1_struct_0(B_761), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_761, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_10653])).
% 29.54/20.61  tff(c_608, plain, (![A_1, A_200, B_199]: (r1_tarski(A_1, u1_struct_0(A_200)) | ~r1_tarski(A_1, u1_struct_0(B_199)) | ~m1_pre_topc(B_199, A_200) | ~v2_pre_topc(A_200) | ~l1_pre_topc(A_200))), inference(resolution, [status(thm)], [c_602, c_2])).
% 29.54/20.61  tff(c_10701, plain, (![B_761, A_200]: (r1_tarski(u1_struct_0(B_761), u1_struct_0(A_200)) | ~m1_pre_topc('#skF_2', A_200) | ~v2_pre_topc(A_200) | ~l1_pre_topc(A_200) | ~m1_pre_topc(B_761, '#skF_2'))), inference(resolution, [status(thm)], [c_10663, c_608])).
% 29.54/20.61  tff(c_10672, plain, (![B_761]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_2'), u1_struct_0(B_761))=k9_relat_1('#skF_4', u1_struct_0(B_761)) | ~m1_pre_topc('#skF_2', '#skF_2') | ~m1_pre_topc(B_761, '#skF_2'))), inference(resolution, [status(thm)], [c_10663, c_1448])).
% 29.54/20.61  tff(c_13537, plain, (![B_846]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_2'), u1_struct_0(B_846))=k9_relat_1('#skF_4', u1_struct_0(B_846)) | ~m1_pre_topc(B_846, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10647, c_10672])).
% 29.54/20.61  tff(c_1440, plain, (![D_297, A_6]: (r1_tarski(k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_297), A_6), k2_relat_1('#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_297))) | ~m1_pre_topc(D_297, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1385])).
% 29.54/20.61  tff(c_13602, plain, (![B_846]: (r1_tarski(k9_relat_1('#skF_4', u1_struct_0(B_846)), k2_relat_1('#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_2'))) | ~m1_pre_topc('#skF_2', '#skF_2') | ~m1_pre_topc(B_846, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_13537, c_1440])).
% 29.54/20.61  tff(c_13655, plain, (![B_846]: (r1_tarski(k9_relat_1('#skF_4', u1_struct_0(B_846)), k2_relat_1('#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_2'))) | ~m1_pre_topc(B_846, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10647, c_13602])).
% 29.54/20.61  tff(c_13849, plain, (~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_13655])).
% 29.54/20.61  tff(c_13852, plain, (~m1_pre_topc('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_1762, c_13849])).
% 29.54/20.61  tff(c_13862, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10647, c_13852])).
% 29.54/20.61  tff(c_13864, plain, (v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_13655])).
% 29.54/20.61  tff(c_186, plain, (![A_123, C_124, B_125]: (k9_relat_1(k7_relat_1(A_123, C_124), B_125)=k9_relat_1(A_123, B_125) | ~r1_tarski(B_125, C_124) | ~v1_relat_1(A_123))), inference(cnfTransformation, [status(thm)], [f_48])).
% 29.54/20.61  tff(c_3904, plain, (![A_474, B_475, C_476]: (r1_tarski(k9_relat_1(A_474, B_475), k2_relat_1(k7_relat_1(A_474, C_476))) | ~v1_relat_1(k7_relat_1(A_474, C_476)) | ~v1_relat_1(k7_relat_1(A_474, C_476)) | ~r1_tarski(B_475, C_476) | ~v1_relat_1(A_474))), inference(superposition, [status(thm), theory('equality')], [c_186, c_132])).
% 29.54/20.61  tff(c_3958, plain, (![B_7, B_475, A_6]: (r1_tarski(k9_relat_1(B_7, B_475), k9_relat_1(B_7, A_6)) | ~v1_relat_1(k7_relat_1(B_7, A_6)) | ~v1_relat_1(k7_relat_1(B_7, A_6)) | ~r1_tarski(B_475, A_6) | ~v1_relat_1(B_7) | ~v1_relat_1(B_7))), inference(superposition, [status(thm), theory('equality')], [c_8, c_3904])).
% 29.54/20.61  tff(c_4, plain, (![B_5, A_4]: (v5_relat_1(B_5, A_4) | ~r1_tarski(k2_relat_1(B_5), A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 29.54/20.61  tff(c_136, plain, (![B_108, A_109]: (v5_relat_1(k7_relat_1(B_108, A_109), k2_relat_1(B_108)) | ~v1_relat_1(k7_relat_1(B_108, A_109)) | ~v1_relat_1(B_108))), inference(resolution, [status(thm)], [c_124, c_4])).
% 29.54/20.61  tff(c_108, plain, (![C_103, B_104, A_105]: (v5_relat_1(C_103, B_104) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_105, B_104))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 29.54/20.61  tff(c_112, plain, (v5_relat_1('#skF_4', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_108])).
% 29.54/20.61  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 29.54/20.61  tff(c_113, plain, (![B_106, A_107]: (r1_tarski(k2_relat_1(B_106), A_107) | ~v5_relat_1(B_106, A_107) | ~v1_relat_1(B_106))), inference(cnfTransformation, [status(thm)], [f_37])).
% 29.54/20.61  tff(c_173, plain, (![A_120, A_121, B_122]: (r1_tarski(A_120, A_121) | ~r1_tarski(A_120, k2_relat_1(B_122)) | ~v5_relat_1(B_122, A_121) | ~v1_relat_1(B_122))), inference(resolution, [status(thm)], [c_113, c_2])).
% 29.54/20.61  tff(c_426, plain, (![B_169, A_170, B_171]: (r1_tarski(k2_relat_1(B_169), A_170) | ~v5_relat_1(B_171, A_170) | ~v1_relat_1(B_171) | ~v5_relat_1(B_169, k2_relat_1(B_171)) | ~v1_relat_1(B_169))), inference(resolution, [status(thm)], [c_6, c_173])).
% 29.54/20.61  tff(c_434, plain, (![B_169]: (r1_tarski(k2_relat_1(B_169), u1_struct_0('#skF_1')) | ~v1_relat_1('#skF_4') | ~v5_relat_1(B_169, k2_relat_1('#skF_4')) | ~v1_relat_1(B_169))), inference(resolution, [status(thm)], [c_112, c_426])).
% 29.54/20.61  tff(c_456, plain, (![B_177]: (r1_tarski(k2_relat_1(B_177), u1_struct_0('#skF_1')) | ~v5_relat_1(B_177, k2_relat_1('#skF_4')) | ~v1_relat_1(B_177))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_434])).
% 29.54/20.61  tff(c_468, plain, (![B_177]: (v5_relat_1(B_177, u1_struct_0('#skF_1')) | ~v5_relat_1(B_177, k2_relat_1('#skF_4')) | ~v1_relat_1(B_177))), inference(resolution, [status(thm)], [c_456, c_4])).
% 29.54/20.61  tff(c_10696, plain, (![B_761]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_2'), u1_struct_0(B_761))=k9_relat_1('#skF_4', u1_struct_0(B_761)) | ~m1_pre_topc(B_761, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10647, c_10672])).
% 29.54/20.61  tff(c_778, plain, (![B_220, A_221, A_222]: (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(B_220, A_221), A_222)), k9_relat_1(B_220, A_221)) | ~v1_relat_1(k7_relat_1(B_220, A_221)) | ~v1_relat_1(B_220))), inference(superposition, [status(thm), theory('equality')], [c_8, c_124])).
% 29.54/20.61  tff(c_2785, plain, (![B_406, A_407, A_408]: (r1_tarski(k9_relat_1(k7_relat_1(B_406, A_407), A_408), k9_relat_1(B_406, A_407)) | ~v1_relat_1(k7_relat_1(B_406, A_407)) | ~v1_relat_1(B_406) | ~v1_relat_1(k7_relat_1(B_406, A_407)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_778])).
% 29.54/20.61  tff(c_2819, plain, (![D_296, A_408]: (r1_tarski(k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_296), A_408), k9_relat_1('#skF_4', u1_struct_0(D_296))) | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_296))) | ~v1_relat_1('#skF_4') | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_296))) | ~m1_pre_topc(D_296, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1329, c_2785])).
% 29.54/20.61  tff(c_21193, plain, (![D_1087, A_1088]: (r1_tarski(k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_1087), A_1088), k9_relat_1('#skF_4', u1_struct_0(D_1087))) | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_1087))) | ~m1_pre_topc(D_1087, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2819])).
% 29.54/20.61  tff(c_21254, plain, (![B_761]: (r1_tarski(k9_relat_1('#skF_4', u1_struct_0(B_761)), k9_relat_1('#skF_4', u1_struct_0('#skF_2'))) | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_2'))) | ~m1_pre_topc('#skF_2', '#skF_2') | ~m1_pre_topc(B_761, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_10696, c_21193])).
% 29.54/20.61  tff(c_23145, plain, (![B_1100]: (r1_tarski(k9_relat_1('#skF_4', u1_struct_0(B_1100)), k9_relat_1('#skF_4', u1_struct_0('#skF_2'))) | ~m1_pre_topc(B_1100, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10647, c_13864, c_21254])).
% 29.54/20.61  tff(c_182, plain, (![A_120, A_121, B_7, A_6]: (r1_tarski(A_120, A_121) | ~r1_tarski(A_120, k9_relat_1(B_7, A_6)) | ~v5_relat_1(k7_relat_1(B_7, A_6), A_121) | ~v1_relat_1(k7_relat_1(B_7, A_6)) | ~v1_relat_1(B_7))), inference(superposition, [status(thm), theory('equality')], [c_8, c_173])).
% 29.54/20.61  tff(c_23200, plain, (![B_1100, A_121]: (r1_tarski(k9_relat_1('#skF_4', u1_struct_0(B_1100)), A_121) | ~v5_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_2')), A_121) | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_2'))) | ~v1_relat_1('#skF_4') | ~m1_pre_topc(B_1100, '#skF_2'))), inference(resolution, [status(thm)], [c_23145, c_182])).
% 29.54/20.61  tff(c_30324, plain, (![B_1182, A_1183]: (r1_tarski(k9_relat_1('#skF_4', u1_struct_0(B_1182)), A_1183) | ~v5_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_2')), A_1183) | ~m1_pre_topc(B_1182, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_13864, c_23200])).
% 29.54/20.61  tff(c_30375, plain, (![B_1182]: (r1_tarski(k9_relat_1('#skF_4', u1_struct_0(B_1182)), u1_struct_0('#skF_1')) | ~m1_pre_topc(B_1182, '#skF_2') | ~v5_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_2')), k2_relat_1('#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_468, c_30324])).
% 29.54/20.61  tff(c_30432, plain, (![B_1182]: (r1_tarski(k9_relat_1('#skF_4', u1_struct_0(B_1182)), u1_struct_0('#skF_1')) | ~m1_pre_topc(B_1182, '#skF_2') | ~v5_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_2')), k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_13864, c_30375])).
% 29.54/20.61  tff(c_44696, plain, (~v5_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_2')), k2_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_30432])).
% 29.54/20.61  tff(c_44714, plain, (~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_2'))) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_136, c_44696])).
% 29.54/20.61  tff(c_44730, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_13864, c_44714])).
% 29.54/20.61  tff(c_44732, plain, (v5_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_2')), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_30432])).
% 29.54/20.61  tff(c_75274, plain, (![B_1803, A_1804]: (r1_tarski(k9_relat_1(B_1803, A_1804), u1_struct_0('#skF_1')) | ~v5_relat_1(k7_relat_1(B_1803, A_1804), k2_relat_1('#skF_4')) | ~v1_relat_1(k7_relat_1(B_1803, A_1804)) | ~v1_relat_1(B_1803))), inference(superposition, [status(thm), theory('equality')], [c_8, c_456])).
% 29.54/20.61  tff(c_75283, plain, (r1_tarski(k9_relat_1('#skF_4', u1_struct_0('#skF_2')), u1_struct_0('#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_2'))) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44732, c_75274])).
% 29.54/20.61  tff(c_75332, plain, (r1_tarski(k9_relat_1('#skF_4', u1_struct_0('#skF_2')), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_13864, c_75283])).
% 29.54/20.61  tff(c_75961, plain, (![A_1809]: (r1_tarski(A_1809, u1_struct_0('#skF_1')) | ~r1_tarski(A_1809, k9_relat_1('#skF_4', u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_75332, c_2])).
% 29.54/20.61  tff(c_76074, plain, (![B_475]: (r1_tarski(k9_relat_1('#skF_4', B_475), u1_struct_0('#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_2'))) | ~r1_tarski(B_475, u1_struct_0('#skF_2')) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_3958, c_75961])).
% 29.54/20.61  tff(c_76749, plain, (![B_1815]: (r1_tarski(k9_relat_1('#skF_4', B_1815), u1_struct_0('#skF_1')) | ~r1_tarski(B_1815, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_13864, c_76074])).
% 29.54/20.61  tff(c_20, plain, (![A_21, B_22, C_23, D_24]: (k7_relset_1(A_21, B_22, C_23, D_24)=k9_relat_1(C_23, D_24) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 29.54/20.61  tff(c_1942, plain, (![B_346, E_342, D_343, D_344, A_345, C_347]: (k7_relset_1(B_346, C_347, k2_partfun1(A_345, D_343, E_342, B_346), D_344)=k9_relat_1(k2_partfun1(A_345, D_343, E_342, B_346), D_344) | ~r1_tarski(k7_relset_1(A_345, D_343, E_342, B_346), C_347) | ~r1_tarski(B_346, A_345) | ~m1_subset_1(E_342, k1_zfmisc_1(k2_zfmisc_1(A_345, D_343))) | ~v1_funct_2(E_342, A_345, D_343) | ~v1_funct_1(E_342) | v1_xboole_0(D_343))), inference(resolution, [status(thm)], [c_1091, c_20])).
% 29.54/20.61  tff(c_1947, plain, (![D_148, C_347, D_344]: (k7_relset_1(D_148, C_347, k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_148), D_344)=k9_relat_1(k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_148), D_344) | ~r1_tarski(k9_relat_1('#skF_4', D_148), C_347) | ~r1_tarski(D_148, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_327, c_1942])).
% 29.54/20.61  tff(c_1953, plain, (![D_148, C_347, D_344]: (k7_relset_1(D_148, C_347, k7_relat_1('#skF_4', D_148), D_344)=k9_relat_1(k7_relat_1('#skF_4', D_148), D_344) | ~r1_tarski(k9_relat_1('#skF_4', D_148), C_347) | ~r1_tarski(D_148, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_446, c_446, c_1947])).
% 29.54/20.61  tff(c_1954, plain, (![D_148, C_347, D_344]: (k7_relset_1(D_148, C_347, k7_relat_1('#skF_4', D_148), D_344)=k9_relat_1(k7_relat_1('#skF_4', D_148), D_344) | ~r1_tarski(k9_relat_1('#skF_4', D_148), C_347) | ~r1_tarski(D_148, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_981, c_1953])).
% 29.54/20.61  tff(c_90438, plain, (![B_1977, D_1978]: (k7_relset_1(B_1977, u1_struct_0('#skF_1'), k7_relat_1('#skF_4', B_1977), D_1978)=k9_relat_1(k7_relat_1('#skF_4', B_1977), D_1978) | ~r1_tarski(B_1977, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_76749, c_1954])).
% 29.54/20.61  tff(c_90725, plain, (![D_1983, D_1984]: (k7_relset_1(u1_struct_0(D_1983), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_1983), D_1984)=k9_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_1983)), D_1984) | ~r1_tarski(u1_struct_0(D_1983), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_1983, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1329, c_90438])).
% 29.54/20.61  tff(c_42, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_185])).
% 29.54/20.61  tff(c_328, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_327, c_42])).
% 29.54/20.61  tff(c_90741, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90725, c_328])).
% 29.54/20.61  tff(c_90752, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_90741])).
% 29.54/20.61  tff(c_90754, plain, (~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_90752])).
% 29.54/20.61  tff(c_90757, plain, (~m1_pre_topc('#skF_2', '#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_10701, c_90754])).
% 29.54/20.61  tff(c_90779, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_58, c_60, c_10647, c_90757])).
% 29.54/20.61  tff(c_90780, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_90752])).
% 29.54/20.61  tff(c_92481, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1329, c_90780])).
% 29.54/20.61  tff(c_92487, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_2224, c_92481])).
% 29.54/20.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.54/20.61  
% 29.54/20.61  Inference rules
% 29.54/20.61  ----------------------
% 29.54/20.61  #Ref     : 0
% 29.54/20.61  #Sup     : 21463
% 29.54/20.61  #Fact    : 0
% 29.54/20.61  #Define  : 0
% 29.54/20.61  #Split   : 56
% 29.54/20.61  #Chain   : 0
% 29.54/20.61  #Close   : 0
% 29.54/20.61  
% 29.54/20.61  Ordering : KBO
% 29.54/20.61  
% 29.54/20.61  Simplification rules
% 29.54/20.61  ----------------------
% 29.54/20.61  #Subsume      : 12316
% 29.54/20.61  #Demod        : 8963
% 29.54/20.61  #Tautology    : 1256
% 29.54/20.61  #SimpNegUnit  : 174
% 29.54/20.61  #BackRed      : 1
% 29.54/20.61  
% 29.54/20.61  #Partial instantiations: 0
% 29.54/20.61  #Strategies tried      : 1
% 29.54/20.61  
% 29.54/20.61  Timing (in seconds)
% 29.54/20.61  ----------------------
% 29.54/20.61  Preprocessing        : 0.35
% 29.54/20.61  Parsing              : 0.19
% 29.54/20.61  CNF conversion       : 0.03
% 29.54/20.61  Main loop            : 19.42
% 29.54/20.61  Inferencing          : 2.79
% 29.54/20.61  Reduction            : 5.84
% 29.54/20.61  Demodulation         : 4.16
% 29.54/20.61  BG Simplification    : 0.19
% 29.54/20.61  Subsumption          : 9.74
% 29.54/20.61  Abstraction          : 0.39
% 29.54/20.61  MUC search           : 0.00
% 29.54/20.61  Cooper               : 0.00
% 29.54/20.61  Total                : 19.84
% 29.54/20.61  Index Insertion      : 0.00
% 29.54/20.61  Index Deletion       : 0.00
% 29.54/20.61  Index Matching       : 0.00
% 29.54/20.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
