%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:16 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 611 expanded)
%              Number of leaves         :   28 ( 248 expanded)
%              Depth                    :   12
%              Number of atoms          :  246 (4443 expanded)
%              Number of equality atoms :    1 (   7 expanded)
%              Maximal formula depth    :   27 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_156,negated_conjecture,(
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
                          & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                       => ( m1_pre_topc(C,D)
                         => r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,k2_tmap_1(A,B,E,D)),k2_tmap_1(A,B,E,C)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tmap_1)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B))))
        & l1_struct_0(D) )
     => ( v1_funct_1(k2_tmap_1(A,B,C,D))
        & v1_funct_2(k2_tmap_1(A,B,C,D),u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(k2_tmap_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_117,axiom,(
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
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,u1_struct_0(C),u1_struct_0(B))
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                         => ( ( r2_funct_2(u1_struct_0(C),u1_struct_0(B),F,k2_tmap_1(A,B,E,C))
                              & m1_pre_topc(D,C) )
                           => r2_funct_2(u1_struct_0(D),u1_struct_0(B),k3_tmap_1(A,B,C,D,F),k2_tmap_1(A,B,E,D)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tmap_1)).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_28,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_48,plain,(
    ! [B_103,A_104] :
      ( l1_pre_topc(B_103)
      | ~ m1_pre_topc(B_103,A_104)
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_54,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_48])).

tff(c_61,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_54])).

tff(c_6,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_26,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_24,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_22,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_73,plain,(
    ! [A_108,B_109,C_110,D_111] :
      ( v1_funct_1(k2_tmap_1(A_108,B_109,C_110,D_111))
      | ~ l1_struct_0(D_111)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_108),u1_struct_0(B_109))))
      | ~ v1_funct_2(C_110,u1_struct_0(A_108),u1_struct_0(B_109))
      | ~ v1_funct_1(C_110)
      | ~ l1_struct_0(B_109)
      | ~ l1_struct_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_75,plain,(
    ! [D_111] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_111))
      | ~ l1_struct_0(D_111)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_73])).

tff(c_78,plain,(
    ! [D_111] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_111))
      | ~ l1_struct_0(D_111)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_75])).

tff(c_79,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_82,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_79])).

tff(c_86,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_82])).

tff(c_88,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_36,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_87,plain,(
    ! [D_111] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_111))
      | ~ l1_struct_0(D_111) ) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_96,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_99,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_96])).

tff(c_103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_99])).

tff(c_105,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_38,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_32,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_20,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_114,plain,(
    ! [A_122,B_123,C_124,D_125] :
      ( m1_subset_1(k2_tmap_1(A_122,B_123,C_124,D_125),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_125),u1_struct_0(B_123))))
      | ~ l1_struct_0(D_125)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_122),u1_struct_0(B_123))))
      | ~ v1_funct_2(C_124,u1_struct_0(A_122),u1_struct_0(B_123))
      | ~ v1_funct_1(C_124)
      | ~ l1_struct_0(B_123)
      | ~ l1_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [A_1,B_2,D_4] :
      ( r2_funct_2(A_1,B_2,D_4,D_4)
      | ~ m1_subset_1(D_4,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(D_4,A_1,B_2)
      | ~ v1_funct_1(D_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_132,plain,(
    ! [D_139,B_140,A_141,C_142] :
      ( r2_funct_2(u1_struct_0(D_139),u1_struct_0(B_140),k2_tmap_1(A_141,B_140,C_142,D_139),k2_tmap_1(A_141,B_140,C_142,D_139))
      | ~ v1_funct_2(k2_tmap_1(A_141,B_140,C_142,D_139),u1_struct_0(D_139),u1_struct_0(B_140))
      | ~ v1_funct_1(k2_tmap_1(A_141,B_140,C_142,D_139))
      | ~ l1_struct_0(D_139)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_141),u1_struct_0(B_140))))
      | ~ v1_funct_2(C_142,u1_struct_0(A_141),u1_struct_0(B_140))
      | ~ v1_funct_1(C_142)
      | ~ l1_struct_0(B_140)
      | ~ l1_struct_0(A_141) ) ),
    inference(resolution,[status(thm)],[c_114,c_2])).

tff(c_16,plain,(
    ! [F_75,E_73,A_13,C_61,B_45,D_69] :
      ( r2_funct_2(u1_struct_0(D_69),u1_struct_0(B_45),k3_tmap_1(A_13,B_45,C_61,D_69,F_75),k2_tmap_1(A_13,B_45,E_73,D_69))
      | ~ m1_pre_topc(D_69,C_61)
      | ~ r2_funct_2(u1_struct_0(C_61),u1_struct_0(B_45),F_75,k2_tmap_1(A_13,B_45,E_73,C_61))
      | ~ m1_subset_1(F_75,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_61),u1_struct_0(B_45))))
      | ~ v1_funct_2(F_75,u1_struct_0(C_61),u1_struct_0(B_45))
      | ~ v1_funct_1(F_75)
      | ~ m1_subset_1(E_73,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_13),u1_struct_0(B_45))))
      | ~ v1_funct_2(E_73,u1_struct_0(A_13),u1_struct_0(B_45))
      | ~ v1_funct_1(E_73)
      | ~ m1_pre_topc(D_69,A_13)
      | v2_struct_0(D_69)
      | ~ m1_pre_topc(C_61,A_13)
      | v2_struct_0(C_61)
      | ~ l1_pre_topc(B_45)
      | ~ v2_pre_topc(B_45)
      | v2_struct_0(B_45)
      | ~ l1_pre_topc(A_13)
      | ~ v2_pre_topc(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_144,plain,(
    ! [D_149,C_151,B_148,A_150,D_152] :
      ( r2_funct_2(u1_struct_0(D_152),u1_struct_0(B_148),k3_tmap_1(A_150,B_148,D_149,D_152,k2_tmap_1(A_150,B_148,C_151,D_149)),k2_tmap_1(A_150,B_148,C_151,D_152))
      | ~ m1_pre_topc(D_152,D_149)
      | ~ m1_subset_1(k2_tmap_1(A_150,B_148,C_151,D_149),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_149),u1_struct_0(B_148))))
      | ~ m1_pre_topc(D_152,A_150)
      | v2_struct_0(D_152)
      | ~ m1_pre_topc(D_149,A_150)
      | v2_struct_0(D_149)
      | ~ l1_pre_topc(B_148)
      | ~ v2_pre_topc(B_148)
      | v2_struct_0(B_148)
      | ~ l1_pre_topc(A_150)
      | ~ v2_pre_topc(A_150)
      | v2_struct_0(A_150)
      | ~ v1_funct_2(k2_tmap_1(A_150,B_148,C_151,D_149),u1_struct_0(D_149),u1_struct_0(B_148))
      | ~ v1_funct_1(k2_tmap_1(A_150,B_148,C_151,D_149))
      | ~ l1_struct_0(D_149)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_150),u1_struct_0(B_148))))
      | ~ v1_funct_2(C_151,u1_struct_0(A_150),u1_struct_0(B_148))
      | ~ v1_funct_1(C_151)
      | ~ l1_struct_0(B_148)
      | ~ l1_struct_0(A_150) ) ),
    inference(resolution,[status(thm)],[c_132,c_16])).

tff(c_18,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_151,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_144,c_18])).

tff(c_156,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1')
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ l1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_105,c_26,c_24,c_22,c_44,c_42,c_38,c_36,c_28,c_32,c_20,c_151])).

tff(c_157,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_40,c_30,c_34,c_156])).

tff(c_158,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_157])).

tff(c_161,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_158])).

tff(c_165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_161])).

tff(c_167,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_107,plain,(
    ! [A_117,B_118,C_119,D_120] :
      ( v1_funct_2(k2_tmap_1(A_117,B_118,C_119,D_120),u1_struct_0(D_120),u1_struct_0(B_118))
      | ~ l1_struct_0(D_120)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_117),u1_struct_0(B_118))))
      | ~ v1_funct_2(C_119,u1_struct_0(A_117),u1_struct_0(B_118))
      | ~ v1_funct_1(C_119)
      | ~ l1_struct_0(B_118)
      | ~ l1_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_109,plain,(
    ! [D_120] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_120),u1_struct_0(D_120),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_120)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_107])).

tff(c_112,plain,(
    ! [D_120] :
      ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_120),u1_struct_0(D_120),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_105,c_26,c_24,c_109])).

tff(c_104,plain,(
    ! [D_111] :
      ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5',D_111))
      | ~ l1_struct_0(D_111) ) ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_10,plain,(
    ! [A_9,B_10,C_11,D_12] :
      ( m1_subset_1(k2_tmap_1(A_9,B_10,C_11,D_12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_12),u1_struct_0(B_10))))
      | ~ l1_struct_0(D_12)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9),u1_struct_0(B_10))))
      | ~ v1_funct_2(C_11,u1_struct_0(A_9),u1_struct_0(B_10))
      | ~ v1_funct_1(C_11)
      | ~ l1_struct_0(B_10)
      | ~ l1_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_166,plain,
    ( ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_168,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_171,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_168])).

tff(c_175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_105,c_26,c_24,c_22,c_167,c_171])).

tff(c_176,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_200,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_203,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_104,c_200])).

tff(c_207,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_203])).

tff(c_208,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_212,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_112,c_208])).

tff(c_216,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_212])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:49:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.40  
% 2.71/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.40  %$ r2_funct_2 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.71/1.40  
% 2.71/1.40  %Foreground sorts:
% 2.71/1.40  
% 2.71/1.40  
% 2.71/1.40  %Background operators:
% 2.71/1.40  
% 2.71/1.40  
% 2.71/1.40  %Foreground operators:
% 2.71/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.71/1.40  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.71/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.71/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.71/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.71/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.71/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.71/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.71/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.71/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.71/1.40  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.71/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.71/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.71/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.40  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.71/1.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.71/1.40  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 2.71/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.71/1.40  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.71/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.71/1.40  
% 2.71/1.42  tff(f_156, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (m1_pre_topc(C, D) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, k2_tmap_1(A, B, E, D)), k2_tmap_1(A, B, E, C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_tmap_1)).
% 2.71/1.42  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.71/1.42  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.71/1.42  tff(f_70, axiom, (![A, B, C, D]: ((((((l1_struct_0(A) & l1_struct_0(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & l1_struct_0(D)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 2.71/1.42  tff(f_41, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 2.71/1.42  tff(f_117, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((r2_funct_2(u1_struct_0(C), u1_struct_0(B), F, k2_tmap_1(A, B, E, C)) & m1_pre_topc(D, C)) => r2_funct_2(u1_struct_0(D), u1_struct_0(B), k3_tmap_1(A, B, C, D, F), k2_tmap_1(A, B, E, D))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tmap_1)).
% 2.71/1.42  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.71/1.42  tff(c_28, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.71/1.42  tff(c_48, plain, (![B_103, A_104]: (l1_pre_topc(B_103) | ~m1_pre_topc(B_103, A_104) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.71/1.42  tff(c_54, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_48])).
% 2.71/1.42  tff(c_61, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_54])).
% 2.71/1.42  tff(c_6, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.71/1.42  tff(c_46, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.71/1.42  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.71/1.42  tff(c_30, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.71/1.42  tff(c_34, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.71/1.42  tff(c_26, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.71/1.42  tff(c_24, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.71/1.42  tff(c_22, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.71/1.42  tff(c_73, plain, (![A_108, B_109, C_110, D_111]: (v1_funct_1(k2_tmap_1(A_108, B_109, C_110, D_111)) | ~l1_struct_0(D_111) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_108), u1_struct_0(B_109)))) | ~v1_funct_2(C_110, u1_struct_0(A_108), u1_struct_0(B_109)) | ~v1_funct_1(C_110) | ~l1_struct_0(B_109) | ~l1_struct_0(A_108))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.71/1.42  tff(c_75, plain, (![D_111]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_111)) | ~l1_struct_0(D_111) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_73])).
% 2.71/1.42  tff(c_78, plain, (![D_111]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_111)) | ~l1_struct_0(D_111) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_75])).
% 2.71/1.42  tff(c_79, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_78])).
% 2.71/1.42  tff(c_82, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_79])).
% 2.71/1.42  tff(c_86, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_82])).
% 2.71/1.42  tff(c_88, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_78])).
% 2.71/1.42  tff(c_36, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.71/1.42  tff(c_87, plain, (![D_111]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_111)) | ~l1_struct_0(D_111))), inference(splitRight, [status(thm)], [c_78])).
% 2.71/1.42  tff(c_96, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_87])).
% 2.71/1.42  tff(c_99, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_96])).
% 2.71/1.42  tff(c_103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_99])).
% 2.71/1.42  tff(c_105, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_87])).
% 2.71/1.42  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.71/1.42  tff(c_38, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.71/1.42  tff(c_32, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.71/1.42  tff(c_20, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.71/1.42  tff(c_114, plain, (![A_122, B_123, C_124, D_125]: (m1_subset_1(k2_tmap_1(A_122, B_123, C_124, D_125), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_125), u1_struct_0(B_123)))) | ~l1_struct_0(D_125) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_122), u1_struct_0(B_123)))) | ~v1_funct_2(C_124, u1_struct_0(A_122), u1_struct_0(B_123)) | ~v1_funct_1(C_124) | ~l1_struct_0(B_123) | ~l1_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.71/1.42  tff(c_2, plain, (![A_1, B_2, D_4]: (r2_funct_2(A_1, B_2, D_4, D_4) | ~m1_subset_1(D_4, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(D_4, A_1, B_2) | ~v1_funct_1(D_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.71/1.42  tff(c_132, plain, (![D_139, B_140, A_141, C_142]: (r2_funct_2(u1_struct_0(D_139), u1_struct_0(B_140), k2_tmap_1(A_141, B_140, C_142, D_139), k2_tmap_1(A_141, B_140, C_142, D_139)) | ~v1_funct_2(k2_tmap_1(A_141, B_140, C_142, D_139), u1_struct_0(D_139), u1_struct_0(B_140)) | ~v1_funct_1(k2_tmap_1(A_141, B_140, C_142, D_139)) | ~l1_struct_0(D_139) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_141), u1_struct_0(B_140)))) | ~v1_funct_2(C_142, u1_struct_0(A_141), u1_struct_0(B_140)) | ~v1_funct_1(C_142) | ~l1_struct_0(B_140) | ~l1_struct_0(A_141))), inference(resolution, [status(thm)], [c_114, c_2])).
% 2.71/1.42  tff(c_16, plain, (![F_75, E_73, A_13, C_61, B_45, D_69]: (r2_funct_2(u1_struct_0(D_69), u1_struct_0(B_45), k3_tmap_1(A_13, B_45, C_61, D_69, F_75), k2_tmap_1(A_13, B_45, E_73, D_69)) | ~m1_pre_topc(D_69, C_61) | ~r2_funct_2(u1_struct_0(C_61), u1_struct_0(B_45), F_75, k2_tmap_1(A_13, B_45, E_73, C_61)) | ~m1_subset_1(F_75, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_61), u1_struct_0(B_45)))) | ~v1_funct_2(F_75, u1_struct_0(C_61), u1_struct_0(B_45)) | ~v1_funct_1(F_75) | ~m1_subset_1(E_73, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_13), u1_struct_0(B_45)))) | ~v1_funct_2(E_73, u1_struct_0(A_13), u1_struct_0(B_45)) | ~v1_funct_1(E_73) | ~m1_pre_topc(D_69, A_13) | v2_struct_0(D_69) | ~m1_pre_topc(C_61, A_13) | v2_struct_0(C_61) | ~l1_pre_topc(B_45) | ~v2_pre_topc(B_45) | v2_struct_0(B_45) | ~l1_pre_topc(A_13) | ~v2_pre_topc(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.71/1.42  tff(c_144, plain, (![D_149, C_151, B_148, A_150, D_152]: (r2_funct_2(u1_struct_0(D_152), u1_struct_0(B_148), k3_tmap_1(A_150, B_148, D_149, D_152, k2_tmap_1(A_150, B_148, C_151, D_149)), k2_tmap_1(A_150, B_148, C_151, D_152)) | ~m1_pre_topc(D_152, D_149) | ~m1_subset_1(k2_tmap_1(A_150, B_148, C_151, D_149), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_149), u1_struct_0(B_148)))) | ~m1_pre_topc(D_152, A_150) | v2_struct_0(D_152) | ~m1_pre_topc(D_149, A_150) | v2_struct_0(D_149) | ~l1_pre_topc(B_148) | ~v2_pre_topc(B_148) | v2_struct_0(B_148) | ~l1_pre_topc(A_150) | ~v2_pre_topc(A_150) | v2_struct_0(A_150) | ~v1_funct_2(k2_tmap_1(A_150, B_148, C_151, D_149), u1_struct_0(D_149), u1_struct_0(B_148)) | ~v1_funct_1(k2_tmap_1(A_150, B_148, C_151, D_149)) | ~l1_struct_0(D_149) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_150), u1_struct_0(B_148)))) | ~v1_funct_2(C_151, u1_struct_0(A_150), u1_struct_0(B_148)) | ~v1_funct_1(C_151) | ~l1_struct_0(B_148) | ~l1_struct_0(A_150))), inference(resolution, [status(thm)], [c_132, c_16])).
% 2.71/1.42  tff(c_18, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.71/1.42  tff(c_151, plain, (~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~l1_struct_0('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_144, c_18])).
% 2.71/1.42  tff(c_156, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1') | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~l1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_105, c_26, c_24, c_22, c_44, c_42, c_38, c_36, c_28, c_32, c_20, c_151])).
% 2.71/1.42  tff(c_157, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_46, c_40, c_30, c_34, c_156])).
% 2.71/1.42  tff(c_158, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_157])).
% 2.71/1.42  tff(c_161, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_6, c_158])).
% 2.71/1.42  tff(c_165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_161])).
% 2.71/1.42  tff(c_167, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_157])).
% 2.71/1.42  tff(c_107, plain, (![A_117, B_118, C_119, D_120]: (v1_funct_2(k2_tmap_1(A_117, B_118, C_119, D_120), u1_struct_0(D_120), u1_struct_0(B_118)) | ~l1_struct_0(D_120) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_117), u1_struct_0(B_118)))) | ~v1_funct_2(C_119, u1_struct_0(A_117), u1_struct_0(B_118)) | ~v1_funct_1(C_119) | ~l1_struct_0(B_118) | ~l1_struct_0(A_117))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.71/1.42  tff(c_109, plain, (![D_120]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_120), u1_struct_0(D_120), u1_struct_0('#skF_2')) | ~l1_struct_0(D_120) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_107])).
% 2.71/1.42  tff(c_112, plain, (![D_120]: (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_120), u1_struct_0(D_120), u1_struct_0('#skF_2')) | ~l1_struct_0(D_120))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_105, c_26, c_24, c_109])).
% 2.71/1.42  tff(c_104, plain, (![D_111]: (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_111)) | ~l1_struct_0(D_111))), inference(splitRight, [status(thm)], [c_87])).
% 2.71/1.42  tff(c_10, plain, (![A_9, B_10, C_11, D_12]: (m1_subset_1(k2_tmap_1(A_9, B_10, C_11, D_12), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_12), u1_struct_0(B_10)))) | ~l1_struct_0(D_12) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9), u1_struct_0(B_10)))) | ~v1_funct_2(C_11, u1_struct_0(A_9), u1_struct_0(B_10)) | ~v1_funct_1(C_11) | ~l1_struct_0(B_10) | ~l1_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.71/1.42  tff(c_166, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_157])).
% 2.71/1.42  tff(c_168, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_166])).
% 2.71/1.42  tff(c_171, plain, (~l1_struct_0('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_10, c_168])).
% 2.71/1.42  tff(c_175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_105, c_26, c_24, c_22, c_167, c_171])).
% 2.71/1.42  tff(c_176, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))), inference(splitRight, [status(thm)], [c_166])).
% 2.71/1.42  tff(c_200, plain, (~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))), inference(splitLeft, [status(thm)], [c_176])).
% 2.71/1.42  tff(c_203, plain, (~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_104, c_200])).
% 2.71/1.42  tff(c_207, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_167, c_203])).
% 2.71/1.42  tff(c_208, plain, (~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_176])).
% 2.71/1.42  tff(c_212, plain, (~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_112, c_208])).
% 2.71/1.42  tff(c_216, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_167, c_212])).
% 2.71/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.42  
% 2.71/1.42  Inference rules
% 2.71/1.42  ----------------------
% 2.71/1.42  #Ref     : 0
% 2.71/1.42  #Sup     : 28
% 2.71/1.42  #Fact    : 0
% 2.71/1.42  #Define  : 0
% 2.71/1.42  #Split   : 5
% 2.71/1.42  #Chain   : 0
% 2.71/1.42  #Close   : 0
% 2.71/1.42  
% 2.71/1.42  Ordering : KBO
% 2.71/1.42  
% 2.71/1.42  Simplification rules
% 2.71/1.42  ----------------------
% 2.71/1.42  #Subsume      : 0
% 2.71/1.42  #Demod        : 53
% 2.71/1.42  #Tautology    : 3
% 2.71/1.42  #SimpNegUnit  : 1
% 2.71/1.42  #BackRed      : 0
% 2.71/1.42  
% 2.71/1.42  #Partial instantiations: 0
% 2.71/1.42  #Strategies tried      : 1
% 2.71/1.42  
% 2.71/1.42  Timing (in seconds)
% 2.71/1.42  ----------------------
% 2.71/1.42  Preprocessing        : 0.33
% 2.71/1.43  Parsing              : 0.18
% 2.71/1.43  CNF conversion       : 0.04
% 2.71/1.43  Main loop            : 0.30
% 2.71/1.43  Inferencing          : 0.12
% 2.71/1.43  Reduction            : 0.08
% 2.71/1.43  Demodulation         : 0.06
% 2.71/1.43  BG Simplification    : 0.02
% 2.71/1.43  Subsumption          : 0.06
% 2.71/1.43  Abstraction          : 0.01
% 2.71/1.43  MUC search           : 0.00
% 2.71/1.43  Cooper               : 0.00
% 2.71/1.43  Total                : 0.68
% 2.71/1.43  Index Insertion      : 0.00
% 2.71/1.43  Index Deletion       : 0.00
% 2.71/1.43  Index Matching       : 0.00
% 2.71/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
