%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:09 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 124 expanded)
%              Number of leaves         :   37 (  63 expanded)
%              Depth                    :   12
%              Number of atoms          :  176 ( 628 expanded)
%              Number of equality atoms :   26 (  54 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_151,negated_conjecture,(
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
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(D),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                       => ( m1_pre_topc(C,D)
                         => ! [F] :
                              ( m1_subset_1(F,u1_struct_0(D))
                             => ( r2_hidden(F,u1_struct_0(C))
                               => k3_funct_2(u1_struct_0(D),u1_struct_0(B),E,F) = k1_funct_1(k3_tmap_1(A,B,D,C,E),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tmap_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_75,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_43,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_107,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ( m1_pre_topc(D,C)
                       => k3_tmap_1(A,B,C,D,E) = k2_partfun1(u1_struct_0(C),u1_struct_0(B),E,u1_struct_0(D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,B)
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).

tff(c_30,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_28,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_26,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_32,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_52,plain,(
    ! [B_109,A_110] :
      ( l1_pre_topc(B_109)
      | ~ m1_pre_topc(B_109,A_110)
      | ~ l1_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_58,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_52])).

tff(c_65,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_58])).

tff(c_10,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_22,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_101,plain,(
    ! [A_123,B_124,C_125,D_126] :
      ( k3_funct_2(A_123,B_124,C_125,D_126) = k1_funct_1(C_125,D_126)
      | ~ m1_subset_1(D_126,A_123)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124)))
      | ~ v1_funct_2(C_125,A_123,B_124)
      | ~ v1_funct_1(C_125)
      | v1_xboole_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_107,plain,(
    ! [B_124,C_125] :
      ( k3_funct_2(u1_struct_0('#skF_4'),B_124,C_125,'#skF_6') = k1_funct_1(C_125,'#skF_6')
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),B_124)))
      | ~ v1_funct_2(C_125,u1_struct_0('#skF_4'),B_124)
      | ~ v1_funct_1(C_125)
      | v1_xboole_0(u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_22,c_101])).

tff(c_108,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_14,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0(u1_struct_0(A_19))
      | ~ l1_struct_0(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_111,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_108,c_14])).

tff(c_114,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_111])).

tff(c_117,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_114])).

tff(c_121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_117])).

tff(c_124,plain,(
    ! [B_127,C_128] :
      ( k3_funct_2(u1_struct_0('#skF_4'),B_127,C_128,'#skF_6') = k1_funct_1(C_128,'#skF_6')
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),B_127)))
      | ~ v1_funct_2(C_128,u1_struct_0('#skF_4'),B_127)
      | ~ v1_funct_1(C_128) ) ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_127,plain,
    ( k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') = k1_funct_1('#skF_5','#skF_6')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_124])).

tff(c_130,plain,(
    k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') = k1_funct_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_127])).

tff(c_18,plain,(
    k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') != k1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_131,plain,(
    k1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k1_funct_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_18])).

tff(c_20,plain,(
    r2_hidden('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_72,plain,(
    ! [C_112,A_113,B_114] :
      ( v1_relat_1(C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_76,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_72])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_24,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_36,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_42,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_86,plain,(
    ! [A_118,B_119,C_120,D_121] :
      ( k2_partfun1(A_118,B_119,C_120,D_121) = k7_relat_1(C_120,D_121)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119)))
      | ~ v1_funct_1(C_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_88,plain,(
    ! [D_121] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_121) = k7_relat_1('#skF_5',D_121)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_26,c_86])).

tff(c_91,plain,(
    ! [D_121] : k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_121) = k7_relat_1('#skF_5',D_121) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_88])).

tff(c_136,plain,(
    ! [D_130,C_133,B_132,A_131,E_129] :
      ( k3_tmap_1(A_131,B_132,C_133,D_130,E_129) = k2_partfun1(u1_struct_0(C_133),u1_struct_0(B_132),E_129,u1_struct_0(D_130))
      | ~ m1_pre_topc(D_130,C_133)
      | ~ m1_subset_1(E_129,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_133),u1_struct_0(B_132))))
      | ~ v1_funct_2(E_129,u1_struct_0(C_133),u1_struct_0(B_132))
      | ~ v1_funct_1(E_129)
      | ~ m1_pre_topc(D_130,A_131)
      | ~ m1_pre_topc(C_133,A_131)
      | ~ l1_pre_topc(B_132)
      | ~ v2_pre_topc(B_132)
      | v2_struct_0(B_132)
      | ~ l1_pre_topc(A_131)
      | ~ v2_pre_topc(A_131)
      | v2_struct_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_138,plain,(
    ! [A_131,D_130] :
      ( k3_tmap_1(A_131,'#skF_2','#skF_4',D_130,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_130))
      | ~ m1_pre_topc(D_130,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_130,A_131)
      | ~ m1_pre_topc('#skF_4',A_131)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_131)
      | ~ v2_pre_topc(A_131)
      | v2_struct_0(A_131) ) ),
    inference(resolution,[status(thm)],[c_26,c_136])).

tff(c_141,plain,(
    ! [D_130,A_131] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_130)) = k3_tmap_1(A_131,'#skF_2','#skF_4',D_130,'#skF_5')
      | ~ m1_pre_topc(D_130,'#skF_4')
      | ~ m1_pre_topc(D_130,A_131)
      | ~ m1_pre_topc('#skF_4',A_131)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_131)
      | ~ v2_pre_topc(A_131)
      | v2_struct_0(A_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_30,c_28,c_91,c_138])).

tff(c_143,plain,(
    ! [D_134,A_135] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_134)) = k3_tmap_1(A_135,'#skF_2','#skF_4',D_134,'#skF_5')
      | ~ m1_pre_topc(D_134,'#skF_4')
      | ~ m1_pre_topc(D_134,A_135)
      | ~ m1_pre_topc('#skF_4',A_135)
      | ~ l1_pre_topc(A_135)
      | ~ v2_pre_topc(A_135)
      | v2_struct_0(A_135) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_141])).

tff(c_149,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_143])).

tff(c_160,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_32,c_24,c_149])).

tff(c_161,plain,(
    k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_160])).

tff(c_2,plain,(
    ! [C_3,B_2,A_1] :
      ( k1_funct_1(k7_relat_1(C_3,B_2),A_1) = k1_funct_1(C_3,A_1)
      | ~ r2_hidden(A_1,B_2)
      | ~ v1_funct_1(C_3)
      | ~ v1_relat_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_165,plain,(
    ! [A_1] :
      ( k1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),A_1) = k1_funct_1('#skF_5',A_1)
      | ~ r2_hidden(A_1,u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_2])).

tff(c_173,plain,(
    ! [A_136] :
      ( k1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),A_136) = k1_funct_1('#skF_5',A_136)
      | ~ r2_hidden(A_136,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_30,c_165])).

tff(c_176,plain,(
    k1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') = k1_funct_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_173])).

tff(c_180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_176])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:06:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.32  
% 2.35/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.33  %$ v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.35/1.33  
% 2.35/1.33  %Foreground sorts:
% 2.35/1.33  
% 2.35/1.33  
% 2.35/1.33  %Background operators:
% 2.35/1.33  
% 2.35/1.33  
% 2.35/1.33  %Foreground operators:
% 2.35/1.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.35/1.33  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.35/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.35/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.35/1.33  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.35/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.35/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.35/1.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.35/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.35/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.35/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.35/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.35/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.35/1.33  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.35/1.33  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.35/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.35/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.35/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.35/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.33  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.35/1.33  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.35/1.33  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.35/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.35/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.35/1.33  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.35/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.35/1.33  
% 2.35/1.34  tff(f_151, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (r2_hidden(F, u1_struct_0(C)) => (k3_funct_2(u1_struct_0(D), u1_struct_0(B), E, F) = k1_funct_1(k3_tmap_1(A, B, D, C, E), F)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_tmap_1)).
% 2.35/1.34  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.35/1.34  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.35/1.34  tff(f_56, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.35/1.34  tff(f_75, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.35/1.34  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.35/1.34  tff(f_43, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.35/1.34  tff(f_107, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 2.35/1.34  tff(f_33, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, B) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_funct_1)).
% 2.35/1.34  tff(c_30, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.35/1.34  tff(c_28, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.35/1.34  tff(c_26, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.35/1.34  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.35/1.34  tff(c_32, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.35/1.34  tff(c_52, plain, (![B_109, A_110]: (l1_pre_topc(B_109) | ~m1_pre_topc(B_109, A_110) | ~l1_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.35/1.34  tff(c_58, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_52])).
% 2.35/1.34  tff(c_65, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_58])).
% 2.35/1.34  tff(c_10, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.35/1.34  tff(c_34, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.35/1.34  tff(c_22, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.35/1.34  tff(c_101, plain, (![A_123, B_124, C_125, D_126]: (k3_funct_2(A_123, B_124, C_125, D_126)=k1_funct_1(C_125, D_126) | ~m1_subset_1(D_126, A_123) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))) | ~v1_funct_2(C_125, A_123, B_124) | ~v1_funct_1(C_125) | v1_xboole_0(A_123))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.35/1.34  tff(c_107, plain, (![B_124, C_125]: (k3_funct_2(u1_struct_0('#skF_4'), B_124, C_125, '#skF_6')=k1_funct_1(C_125, '#skF_6') | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), B_124))) | ~v1_funct_2(C_125, u1_struct_0('#skF_4'), B_124) | ~v1_funct_1(C_125) | v1_xboole_0(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_22, c_101])).
% 2.35/1.34  tff(c_108, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_107])).
% 2.35/1.34  tff(c_14, plain, (![A_19]: (~v1_xboole_0(u1_struct_0(A_19)) | ~l1_struct_0(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.35/1.34  tff(c_111, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_108, c_14])).
% 2.35/1.34  tff(c_114, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_34, c_111])).
% 2.35/1.34  tff(c_117, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_10, c_114])).
% 2.35/1.34  tff(c_121, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_117])).
% 2.35/1.34  tff(c_124, plain, (![B_127, C_128]: (k3_funct_2(u1_struct_0('#skF_4'), B_127, C_128, '#skF_6')=k1_funct_1(C_128, '#skF_6') | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), B_127))) | ~v1_funct_2(C_128, u1_struct_0('#skF_4'), B_127) | ~v1_funct_1(C_128))), inference(splitRight, [status(thm)], [c_107])).
% 2.35/1.34  tff(c_127, plain, (k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')=k1_funct_1('#skF_5', '#skF_6') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_26, c_124])).
% 2.35/1.34  tff(c_130, plain, (k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')=k1_funct_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_127])).
% 2.35/1.34  tff(c_18, plain, (k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')!=k1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.35/1.34  tff(c_131, plain, (k1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_18])).
% 2.35/1.34  tff(c_20, plain, (r2_hidden('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.35/1.34  tff(c_72, plain, (![C_112, A_113, B_114]: (v1_relat_1(C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.35/1.34  tff(c_76, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_26, c_72])).
% 2.35/1.34  tff(c_50, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.35/1.34  tff(c_48, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.35/1.34  tff(c_24, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.35/1.34  tff(c_36, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.35/1.34  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.35/1.34  tff(c_42, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.35/1.34  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.35/1.34  tff(c_86, plain, (![A_118, B_119, C_120, D_121]: (k2_partfun1(A_118, B_119, C_120, D_121)=k7_relat_1(C_120, D_121) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))) | ~v1_funct_1(C_120))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.35/1.34  tff(c_88, plain, (![D_121]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_121)=k7_relat_1('#skF_5', D_121) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_26, c_86])).
% 2.35/1.34  tff(c_91, plain, (![D_121]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_121)=k7_relat_1('#skF_5', D_121))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_88])).
% 2.35/1.34  tff(c_136, plain, (![D_130, C_133, B_132, A_131, E_129]: (k3_tmap_1(A_131, B_132, C_133, D_130, E_129)=k2_partfun1(u1_struct_0(C_133), u1_struct_0(B_132), E_129, u1_struct_0(D_130)) | ~m1_pre_topc(D_130, C_133) | ~m1_subset_1(E_129, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_133), u1_struct_0(B_132)))) | ~v1_funct_2(E_129, u1_struct_0(C_133), u1_struct_0(B_132)) | ~v1_funct_1(E_129) | ~m1_pre_topc(D_130, A_131) | ~m1_pre_topc(C_133, A_131) | ~l1_pre_topc(B_132) | ~v2_pre_topc(B_132) | v2_struct_0(B_132) | ~l1_pre_topc(A_131) | ~v2_pre_topc(A_131) | v2_struct_0(A_131))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.35/1.34  tff(c_138, plain, (![A_131, D_130]: (k3_tmap_1(A_131, '#skF_2', '#skF_4', D_130, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_130)) | ~m1_pre_topc(D_130, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_130, A_131) | ~m1_pre_topc('#skF_4', A_131) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_131) | ~v2_pre_topc(A_131) | v2_struct_0(A_131))), inference(resolution, [status(thm)], [c_26, c_136])).
% 2.35/1.34  tff(c_141, plain, (![D_130, A_131]: (k7_relat_1('#skF_5', u1_struct_0(D_130))=k3_tmap_1(A_131, '#skF_2', '#skF_4', D_130, '#skF_5') | ~m1_pre_topc(D_130, '#skF_4') | ~m1_pre_topc(D_130, A_131) | ~m1_pre_topc('#skF_4', A_131) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_131) | ~v2_pre_topc(A_131) | v2_struct_0(A_131))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_30, c_28, c_91, c_138])).
% 2.35/1.34  tff(c_143, plain, (![D_134, A_135]: (k7_relat_1('#skF_5', u1_struct_0(D_134))=k3_tmap_1(A_135, '#skF_2', '#skF_4', D_134, '#skF_5') | ~m1_pre_topc(D_134, '#skF_4') | ~m1_pre_topc(D_134, A_135) | ~m1_pre_topc('#skF_4', A_135) | ~l1_pre_topc(A_135) | ~v2_pre_topc(A_135) | v2_struct_0(A_135))), inference(negUnitSimplification, [status(thm)], [c_44, c_141])).
% 2.35/1.34  tff(c_149, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_143])).
% 2.35/1.34  tff(c_160, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_32, c_24, c_149])).
% 2.35/1.34  tff(c_161, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_50, c_160])).
% 2.35/1.34  tff(c_2, plain, (![C_3, B_2, A_1]: (k1_funct_1(k7_relat_1(C_3, B_2), A_1)=k1_funct_1(C_3, A_1) | ~r2_hidden(A_1, B_2) | ~v1_funct_1(C_3) | ~v1_relat_1(C_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.35/1.34  tff(c_165, plain, (![A_1]: (k1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), A_1)=k1_funct_1('#skF_5', A_1) | ~r2_hidden(A_1, u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_161, c_2])).
% 2.35/1.34  tff(c_173, plain, (![A_136]: (k1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), A_136)=k1_funct_1('#skF_5', A_136) | ~r2_hidden(A_136, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_30, c_165])).
% 2.35/1.34  tff(c_176, plain, (k1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')=k1_funct_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_20, c_173])).
% 2.35/1.34  tff(c_180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131, c_176])).
% 2.35/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.34  
% 2.35/1.34  Inference rules
% 2.35/1.34  ----------------------
% 2.35/1.34  #Ref     : 0
% 2.35/1.34  #Sup     : 24
% 2.35/1.34  #Fact    : 0
% 2.35/1.34  #Define  : 0
% 2.35/1.34  #Split   : 2
% 2.35/1.34  #Chain   : 0
% 2.35/1.34  #Close   : 0
% 2.35/1.34  
% 2.35/1.34  Ordering : KBO
% 2.35/1.34  
% 2.35/1.34  Simplification rules
% 2.35/1.34  ----------------------
% 2.35/1.34  #Subsume      : 1
% 2.35/1.34  #Demod        : 26
% 2.35/1.34  #Tautology    : 9
% 2.35/1.34  #SimpNegUnit  : 6
% 2.35/1.34  #BackRed      : 1
% 2.35/1.34  
% 2.35/1.34  #Partial instantiations: 0
% 2.35/1.34  #Strategies tried      : 1
% 2.35/1.34  
% 2.35/1.34  Timing (in seconds)
% 2.35/1.34  ----------------------
% 2.35/1.35  Preprocessing        : 0.34
% 2.35/1.35  Parsing              : 0.18
% 2.35/1.35  CNF conversion       : 0.03
% 2.35/1.35  Main loop            : 0.18
% 2.35/1.35  Inferencing          : 0.07
% 2.35/1.35  Reduction            : 0.06
% 2.35/1.35  Demodulation         : 0.04
% 2.35/1.35  BG Simplification    : 0.01
% 2.35/1.35  Subsumption          : 0.03
% 2.35/1.35  Abstraction          : 0.01
% 2.35/1.35  MUC search           : 0.00
% 2.35/1.35  Cooper               : 0.00
% 2.35/1.35  Total                : 0.56
% 2.35/1.35  Index Insertion      : 0.00
% 2.35/1.35  Index Deletion       : 0.00
% 2.35/1.35  Index Matching       : 0.00
% 2.35/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
