%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1782+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:22 EST 2020

% Result     : Theorem 8.40s
% Output     : CNFRefutation 8.80s
% Verified   : 
% Statistics : Number of formulae       :  121 (3589 expanded)
%              Number of leaves         :   41 (1347 expanded)
%              Depth                    :   25
%              Number of atoms          :  360 (15422 expanded)
%              Number of equality atoms :   23 (1028 expanded)
%              Maximal formula depth    :   27 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > r2_funct_2 > v1_funct_2 > v1_partfun1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k4_relset_1 > k1_partfun1 > k2_tmap_1 > k5_relat_1 > k4_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_partfun1 > k3_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k4_tmap_1,type,(
    k4_tmap_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(k3_struct_0,type,(
    k3_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_195,negated_conjecture,(
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
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,u1_struct_0(A),u1_struct_0(B))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                   => r2_funct_2(u1_struct_0(C),u1_struct_0(B),k2_tmap_1(A,B,D,C),k1_partfun1(u1_struct_0(C),u1_struct_0(A),u1_struct_0(A),u1_struct_0(B),k4_tmap_1(A,C),D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_tmap_1)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_28,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k3_struct_0(A) = k6_partfun1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_struct_0)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_105,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_119,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( r2_relset_1(A,B,k4_relset_1(A,A,A,B,k6_partfun1(A),C),C)
        & r2_relset_1(A,B,k4_relset_1(A,B,B,B,C,k6_partfun1(B)),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_2)).

tff(f_113,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ( v1_funct_1(k3_struct_0(A))
        & v1_funct_2(k3_struct_0(A),u1_struct_0(A),u1_struct_0(A))
        & m1_subset_1(k3_struct_0(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_struct_0)).

tff(f_99,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_164,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & v2_pre_topc(C)
                & l1_pre_topc(C) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,u1_struct_0(B),u1_struct_0(C))
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(C)))) )
                         => r2_funct_2(u1_struct_0(D),u1_struct_0(C),k2_tmap_1(A,C,k1_partfun1(u1_struct_0(A),u1_struct_0(B),u1_struct_0(B),u1_struct_0(C),E,F),D),k1_partfun1(u1_struct_0(D),u1_struct_0(B),u1_struct_0(B),u1_struct_0(C),k2_tmap_1(A,B,E,D),F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tmap_1)).

tff(f_40,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => k4_tmap_1(A,B) = k2_tmap_1(A,A,k3_struct_0(A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tmap_1)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_48,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_60,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_58,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_54,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_18,plain,(
    ! [A_13] :
      ( l1_struct_0(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2,plain,(
    ! [A_1] :
      ( k6_partfun1(u1_struct_0(A_1)) = k3_struct_0(A_1)
      | ~ l1_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_16,plain,(
    ! [A_12] : m1_subset_1(k6_partfun1(A_12),k1_zfmisc_1(k2_zfmisc_1(A_12,A_12))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_162,plain,(
    ! [D_141,A_143,B_142,C_145,E_146,F_144] :
      ( k4_relset_1(A_143,B_142,C_145,D_141,E_146,F_144) = k5_relat_1(E_146,F_144)
      | ~ m1_subset_1(F_144,k1_zfmisc_1(k2_zfmisc_1(C_145,D_141)))
      | ~ m1_subset_1(E_146,k1_zfmisc_1(k2_zfmisc_1(A_143,B_142))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_172,plain,(
    ! [A_147,B_148,E_149] :
      ( k4_relset_1(A_147,B_148,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),E_149,'#skF_4') = k5_relat_1(E_149,'#skF_4')
      | ~ m1_subset_1(E_149,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148))) ) ),
    inference(resolution,[status(thm)],[c_42,c_162])).

tff(c_221,plain,(
    ! [A_156] : k4_relset_1(A_156,A_156,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k6_partfun1(A_156),'#skF_4') = k5_relat_1(k6_partfun1(A_156),'#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_172])).

tff(c_12,plain,(
    ! [B_7,D_9,C_8,F_11,E_10,A_6] :
      ( m1_subset_1(k4_relset_1(A_6,B_7,C_8,D_9,E_10,F_11),k1_zfmisc_1(k2_zfmisc_1(A_6,D_9)))
      | ~ m1_subset_1(F_11,k1_zfmisc_1(k2_zfmisc_1(C_8,D_9)))
      | ~ m1_subset_1(E_10,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_227,plain,(
    ! [A_156] :
      ( m1_subset_1(k5_relat_1(k6_partfun1(A_156),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(A_156,u1_struct_0('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ m1_subset_1(k6_partfun1(A_156),k1_zfmisc_1(k2_zfmisc_1(A_156,A_156))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_12])).

tff(c_240,plain,(
    ! [A_156] : m1_subset_1(k5_relat_1(k6_partfun1(A_156),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(A_156,u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_42,c_227])).

tff(c_36,plain,(
    ! [A_36,B_37,C_38] :
      ( r2_relset_1(A_36,B_37,k4_relset_1(A_36,A_36,A_36,B_37,k6_partfun1(A_36),C_38),C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_231,plain,
    ( r2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k5_relat_1(k6_partfun1(u1_struct_0('#skF_1')),'#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_36])).

tff(c_242,plain,(
    r2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k5_relat_1(k6_partfun1(u1_struct_0('#skF_1')),'#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_231])).

tff(c_32,plain,(
    ! [D_35,C_34,A_32,B_33] :
      ( D_35 = C_34
      | ~ r2_relset_1(A_32,B_33,C_34,D_35)
      | ~ m1_subset_1(D_35,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_273,plain,
    ( k5_relat_1(k6_partfun1(u1_struct_0('#skF_1')),'#skF_4') = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ m1_subset_1(k5_relat_1(k6_partfun1(u1_struct_0('#skF_1')),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_242,c_32])).

tff(c_279,plain,(
    k5_relat_1(k6_partfun1(u1_struct_0('#skF_1')),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_42,c_273])).

tff(c_289,plain,
    ( k5_relat_1(k3_struct_0('#skF_1'),'#skF_4') = '#skF_4'
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_279])).

tff(c_293,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_289])).

tff(c_296,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_293])).

tff(c_300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_296])).

tff(c_302,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_289])).

tff(c_10,plain,(
    ! [A_5] :
      ( v1_funct_1(k3_struct_0(A_5))
      | ~ l1_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_44,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_303,plain,(
    ! [A_163,E_162,C_159,D_161,B_160,F_164] :
      ( k1_partfun1(A_163,B_160,C_159,D_161,E_162,F_164) = k5_relat_1(E_162,F_164)
      | ~ m1_subset_1(F_164,k1_zfmisc_1(k2_zfmisc_1(C_159,D_161)))
      | ~ v1_funct_1(F_164)
      | ~ m1_subset_1(E_162,k1_zfmisc_1(k2_zfmisc_1(A_163,B_160)))
      | ~ v1_funct_1(E_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_313,plain,(
    ! [A_163,B_160,E_162] :
      ( k1_partfun1(A_163,B_160,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),E_162,'#skF_4') = k5_relat_1(E_162,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_162,k1_zfmisc_1(k2_zfmisc_1(A_163,B_160)))
      | ~ v1_funct_1(E_162) ) ),
    inference(resolution,[status(thm)],[c_42,c_303])).

tff(c_892,plain,(
    ! [A_209,B_210,E_211] :
      ( k1_partfun1(A_209,B_210,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),E_211,'#skF_4') = k5_relat_1(E_211,'#skF_4')
      | ~ m1_subset_1(E_211,k1_zfmisc_1(k2_zfmisc_1(A_209,B_210)))
      | ~ v1_funct_1(E_211) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_313])).

tff(c_1516,plain,(
    ! [A_242] :
      ( k1_partfun1(A_242,A_242,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k6_partfun1(A_242),'#skF_4') = k5_relat_1(k6_partfun1(A_242),'#skF_4')
      | ~ v1_funct_1(k6_partfun1(A_242)) ) ),
    inference(resolution,[status(thm)],[c_16,c_892])).

tff(c_38,plain,(
    ! [E_99,D_95,F_101,C_87,A_39,B_71] :
      ( r2_funct_2(u1_struct_0(D_95),u1_struct_0(C_87),k2_tmap_1(A_39,C_87,k1_partfun1(u1_struct_0(A_39),u1_struct_0(B_71),u1_struct_0(B_71),u1_struct_0(C_87),E_99,F_101),D_95),k1_partfun1(u1_struct_0(D_95),u1_struct_0(B_71),u1_struct_0(B_71),u1_struct_0(C_87),k2_tmap_1(A_39,B_71,E_99,D_95),F_101))
      | ~ m1_subset_1(F_101,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_71),u1_struct_0(C_87))))
      | ~ v1_funct_2(F_101,u1_struct_0(B_71),u1_struct_0(C_87))
      | ~ v1_funct_1(F_101)
      | ~ m1_subset_1(E_99,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_39),u1_struct_0(B_71))))
      | ~ v1_funct_2(E_99,u1_struct_0(A_39),u1_struct_0(B_71))
      | ~ v1_funct_1(E_99)
      | ~ m1_pre_topc(D_95,A_39)
      | v2_struct_0(D_95)
      | ~ l1_pre_topc(C_87)
      | ~ v2_pre_topc(C_87)
      | v2_struct_0(C_87)
      | ~ l1_pre_topc(B_71)
      | ~ v2_pre_topc(B_71)
      | v2_struct_0(B_71)
      | ~ l1_pre_topc(A_39)
      | ~ v2_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_1523,plain,(
    ! [D_95] :
      ( r2_funct_2(u1_struct_0(D_95),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1(u1_struct_0('#skF_1')),'#skF_4'),D_95),k1_partfun1(u1_struct_0(D_95),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_1',k6_partfun1(u1_struct_0('#skF_1')),D_95),'#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_1')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_1')),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_1')))
      | ~ m1_pre_topc(D_95,'#skF_1')
      | v2_struct_0(D_95)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1516,c_38])).

tff(c_1532,plain,(
    ! [D_95] :
      ( r2_funct_2(u1_struct_0(D_95),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4',D_95),k1_partfun1(u1_struct_0(D_95),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_1',k6_partfun1(u1_struct_0('#skF_1')),D_95),'#skF_4'))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_1')),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))
      | ~ m1_pre_topc(D_95,'#skF_1')
      | v2_struct_0(D_95)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1')
      | ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_60,c_58,c_54,c_52,c_16,c_46,c_44,c_42,c_279,c_1523])).

tff(c_1533,plain,(
    ! [D_95] :
      ( r2_funct_2(u1_struct_0(D_95),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4',D_95),k1_partfun1(u1_struct_0(D_95),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_1',k6_partfun1(u1_struct_0('#skF_1')),D_95),'#skF_4'))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_1')),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))
      | ~ m1_pre_topc(D_95,'#skF_1')
      | v2_struct_0(D_95)
      | ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_1532])).

tff(c_1646,plain,(
    ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1533])).

tff(c_1649,plain,
    ( ~ v1_funct_1(k3_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1646])).

tff(c_1651,plain,(
    ~ v1_funct_1(k3_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_1649])).

tff(c_1654,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_1651])).

tff(c_1658,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_1654])).

tff(c_1660,plain,(
    v1_funct_1(k6_partfun1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1533])).

tff(c_1663,plain,
    ( v1_funct_1(k3_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1660])).

tff(c_1665,plain,(
    v1_funct_1(k3_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_1663])).

tff(c_8,plain,(
    ! [A_5] :
      ( v1_funct_2(k3_struct_0(A_5),u1_struct_0(A_5),u1_struct_0(A_5))
      | ~ l1_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_301,plain,(
    k5_relat_1(k3_struct_0('#skF_1'),'#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_289])).

tff(c_6,plain,(
    ! [A_5] :
      ( m1_subset_1(k3_struct_0(A_5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5),u1_struct_0(A_5))))
      | ~ l1_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_7243,plain,(
    ! [A_462] :
      ( k1_partfun1(u1_struct_0(A_462),u1_struct_0(A_462),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k3_struct_0(A_462),'#skF_4') = k5_relat_1(k3_struct_0(A_462),'#skF_4')
      | ~ v1_funct_1(k3_struct_0(A_462))
      | ~ l1_struct_0(A_462) ) ),
    inference(resolution,[status(thm)],[c_6,c_892])).

tff(c_4,plain,(
    ! [A_2,B_4] :
      ( k2_tmap_1(A_2,A_2,k3_struct_0(A_2),B_4) = k4_tmap_1(A_2,B_4)
      | ~ m1_pre_topc(B_4,A_2)
      | ~ l1_pre_topc(A_2)
      | ~ v2_pre_topc(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_755,plain,(
    ! [A_195,D_196,C_199,E_194,B_198,F_197] :
      ( r2_funct_2(u1_struct_0(D_196),u1_struct_0(C_199),k2_tmap_1(A_195,C_199,k1_partfun1(u1_struct_0(A_195),u1_struct_0(B_198),u1_struct_0(B_198),u1_struct_0(C_199),E_194,F_197),D_196),k1_partfun1(u1_struct_0(D_196),u1_struct_0(B_198),u1_struct_0(B_198),u1_struct_0(C_199),k2_tmap_1(A_195,B_198,E_194,D_196),F_197))
      | ~ m1_subset_1(F_197,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_198),u1_struct_0(C_199))))
      | ~ v1_funct_2(F_197,u1_struct_0(B_198),u1_struct_0(C_199))
      | ~ v1_funct_1(F_197)
      | ~ m1_subset_1(E_194,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_195),u1_struct_0(B_198))))
      | ~ v1_funct_2(E_194,u1_struct_0(A_195),u1_struct_0(B_198))
      | ~ v1_funct_1(E_194)
      | ~ m1_pre_topc(D_196,A_195)
      | v2_struct_0(D_196)
      | ~ l1_pre_topc(C_199)
      | ~ v2_pre_topc(C_199)
      | v2_struct_0(C_199)
      | ~ l1_pre_topc(B_198)
      | ~ v2_pre_topc(B_198)
      | v2_struct_0(B_198)
      | ~ l1_pre_topc(A_195)
      | ~ v2_pre_topc(A_195)
      | v2_struct_0(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_758,plain,(
    ! [B_4,C_199,A_2,F_197] :
      ( r2_funct_2(u1_struct_0(B_4),u1_struct_0(C_199),k2_tmap_1(A_2,C_199,k1_partfun1(u1_struct_0(A_2),u1_struct_0(A_2),u1_struct_0(A_2),u1_struct_0(C_199),k3_struct_0(A_2),F_197),B_4),k1_partfun1(u1_struct_0(B_4),u1_struct_0(A_2),u1_struct_0(A_2),u1_struct_0(C_199),k4_tmap_1(A_2,B_4),F_197))
      | ~ m1_subset_1(F_197,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2),u1_struct_0(C_199))))
      | ~ v1_funct_2(F_197,u1_struct_0(A_2),u1_struct_0(C_199))
      | ~ v1_funct_1(F_197)
      | ~ m1_subset_1(k3_struct_0(A_2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2),u1_struct_0(A_2))))
      | ~ v1_funct_2(k3_struct_0(A_2),u1_struct_0(A_2),u1_struct_0(A_2))
      | ~ v1_funct_1(k3_struct_0(A_2))
      | ~ m1_pre_topc(B_4,A_2)
      | v2_struct_0(B_4)
      | ~ l1_pre_topc(C_199)
      | ~ v2_pre_topc(C_199)
      | v2_struct_0(C_199)
      | ~ l1_pre_topc(A_2)
      | ~ v2_pre_topc(A_2)
      | v2_struct_0(A_2)
      | ~ l1_pre_topc(A_2)
      | ~ v2_pre_topc(A_2)
      | v2_struct_0(A_2)
      | ~ m1_pre_topc(B_4,A_2)
      | ~ l1_pre_topc(A_2)
      | ~ v2_pre_topc(A_2)
      | v2_struct_0(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_755])).

tff(c_7250,plain,(
    ! [B_4] :
      ( r2_funct_2(u1_struct_0(B_4),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2',k5_relat_1(k3_struct_0('#skF_1'),'#skF_4'),B_4),k1_partfun1(u1_struct_0(B_4),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_1',B_4),'#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(k3_struct_0('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2(k3_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1(k3_struct_0('#skF_1'))
      | ~ m1_pre_topc(B_4,'#skF_1')
      | v2_struct_0(B_4)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ m1_pre_topc(B_4,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ v1_funct_1(k3_struct_0('#skF_1'))
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7243,c_758])).

tff(c_7260,plain,(
    ! [B_4] :
      ( r2_funct_2(u1_struct_0(B_4),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4',B_4),k1_partfun1(u1_struct_0(B_4),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_1',B_4),'#skF_4'))
      | ~ m1_subset_1(k3_struct_0('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2(k3_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))
      | v2_struct_0(B_4)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_4,'#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_1665,c_60,c_58,c_60,c_58,c_60,c_58,c_54,c_52,c_1665,c_46,c_44,c_42,c_301,c_7250])).

tff(c_7261,plain,(
    ! [B_4] :
      ( r2_funct_2(u1_struct_0(B_4),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4',B_4),k1_partfun1(u1_struct_0(B_4),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_1',B_4),'#skF_4'))
      | ~ m1_subset_1(k3_struct_0('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2(k3_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))
      | v2_struct_0(B_4)
      | ~ m1_pre_topc(B_4,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_7260])).

tff(c_7353,plain,(
    ~ v1_funct_2(k3_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_7261])).

tff(c_7356,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_7353])).

tff(c_7360,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_7356])).

tff(c_7362,plain,(
    v1_funct_2(k3_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_7261])).

tff(c_7254,plain,(
    ! [D_95] :
      ( r2_funct_2(u1_struct_0(D_95),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2',k5_relat_1(k3_struct_0('#skF_1'),'#skF_4'),D_95),k1_partfun1(u1_struct_0(D_95),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_1',k3_struct_0('#skF_1'),D_95),'#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(k3_struct_0('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2(k3_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1(k3_struct_0('#skF_1'))
      | ~ m1_pre_topc(D_95,'#skF_1')
      | v2_struct_0(D_95)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ v1_funct_1(k3_struct_0('#skF_1'))
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7243,c_38])).

tff(c_7263,plain,(
    ! [D_95] :
      ( r2_funct_2(u1_struct_0(D_95),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4',D_95),k1_partfun1(u1_struct_0(D_95),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_1',k3_struct_0('#skF_1'),D_95),'#skF_4'))
      | ~ m1_subset_1(k3_struct_0('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2(k3_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))
      | ~ m1_pre_topc(D_95,'#skF_1')
      | v2_struct_0(D_95)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_1665,c_60,c_58,c_60,c_58,c_54,c_52,c_1665,c_46,c_44,c_42,c_301,c_7254])).

tff(c_7264,plain,(
    ! [D_95] :
      ( r2_funct_2(u1_struct_0(D_95),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4',D_95),k1_partfun1(u1_struct_0(D_95),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_1',k3_struct_0('#skF_1'),D_95),'#skF_4'))
      | ~ m1_subset_1(k3_struct_0('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2(k3_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))
      | ~ m1_pre_topc(D_95,'#skF_1')
      | v2_struct_0(D_95) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_7263])).

tff(c_7646,plain,(
    ! [D_95] :
      ( r2_funct_2(u1_struct_0(D_95),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4',D_95),k1_partfun1(u1_struct_0(D_95),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_1',k3_struct_0('#skF_1'),D_95),'#skF_4'))
      | ~ m1_subset_1(k3_struct_0('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))))
      | ~ m1_pre_topc(D_95,'#skF_1')
      | v2_struct_0(D_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7362,c_7264])).

tff(c_7647,plain,(
    ~ m1_subset_1(k3_struct_0('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_7646])).

tff(c_7650,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_7647])).

tff(c_7654,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_7650])).

tff(c_7656,plain,(
    m1_subset_1(k3_struct_0('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_7646])).

tff(c_322,plain,(
    ! [A_163,B_160,E_162] :
      ( k1_partfun1(A_163,B_160,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),E_162,'#skF_4') = k5_relat_1(E_162,'#skF_4')
      | ~ m1_subset_1(E_162,k1_zfmisc_1(k2_zfmisc_1(A_163,B_160)))
      | ~ v1_funct_1(E_162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_313])).

tff(c_7671,plain,
    ( k1_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k3_struct_0('#skF_1'),'#skF_4') = k5_relat_1(k3_struct_0('#skF_1'),'#skF_4')
    | ~ v1_funct_1(k3_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_7656,c_322])).

tff(c_7698,plain,(
    k1_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k3_struct_0('#skF_1'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1665,c_301,c_7671])).

tff(c_7727,plain,(
    ! [B_4] :
      ( r2_funct_2(u1_struct_0(B_4),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4',B_4),k1_partfun1(u1_struct_0(B_4),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_1',B_4),'#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(k3_struct_0('#skF_1'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2(k3_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1(k3_struct_0('#skF_1'))
      | ~ m1_pre_topc(B_4,'#skF_1')
      | v2_struct_0(B_4)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ m1_pre_topc(B_4,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7698,c_758])).

tff(c_7739,plain,(
    ! [B_4] :
      ( r2_funct_2(u1_struct_0(B_4),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4',B_4),k1_partfun1(u1_struct_0(B_4),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_1',B_4),'#skF_4'))
      | v2_struct_0(B_4)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_4,'#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_60,c_58,c_60,c_58,c_54,c_52,c_1665,c_7362,c_7656,c_46,c_44,c_42,c_7727])).

tff(c_8603,plain,(
    ! [B_474] :
      ( r2_funct_2(u1_struct_0(B_474),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4',B_474),k1_partfun1(u1_struct_0(B_474),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_1',B_474),'#skF_4'))
      | v2_struct_0(B_474)
      | ~ m1_pre_topc(B_474,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_7739])).

tff(c_40,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_1','#skF_3'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_8606,plain,
    ( v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_8603,c_40])).

tff(c_8609,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_8606])).

tff(c_8611,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_8609])).

%------------------------------------------------------------------------------
