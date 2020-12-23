%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:09 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 126 expanded)
%              Number of leaves         :   36 (  63 expanded)
%              Depth                    :   12
%              Number of atoms          :  183 ( 654 expanded)
%              Number of equality atoms :   26 (  55 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_153,negated_conjecture,(
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

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_102,axiom,(
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

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,B)
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).

tff(c_30,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_28,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_26,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_24,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_20,plain,(
    r2_hidden('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_32,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_51,plain,(
    ! [B_112,A_113] :
      ( l1_pre_topc(B_112)
      | ~ m1_pre_topc(B_112,A_113)
      | ~ l1_pre_topc(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_57,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_51])).

tff(c_64,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_57])).

tff(c_22,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_109,plain,(
    ! [A_133,B_134,C_135,D_136] :
      ( k3_funct_2(A_133,B_134,C_135,D_136) = k1_funct_1(C_135,D_136)
      | ~ m1_subset_1(D_136,A_133)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134)))
      | ~ v1_funct_2(C_135,A_133,B_134)
      | ~ v1_funct_1(C_135)
      | v1_xboole_0(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_118,plain,(
    ! [B_134,C_135] :
      ( k3_funct_2(u1_struct_0('#skF_4'),B_134,C_135,'#skF_6') = k1_funct_1(C_135,'#skF_6')
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),B_134)))
      | ~ v1_funct_2(C_135,u1_struct_0('#skF_4'),B_134)
      | ~ v1_funct_1(C_135)
      | v1_xboole_0(u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_22,c_109])).

tff(c_119,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_80,plain,(
    ! [B_120,A_121] :
      ( m1_subset_1(u1_struct_0(B_120),k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ m1_pre_topc(B_120,A_121)
      | ~ l1_pre_topc(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2,plain,(
    ! [C_3,B_2,A_1] :
      ( ~ v1_xboole_0(C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_83,plain,(
    ! [A_121,A_1,B_120] :
      ( ~ v1_xboole_0(u1_struct_0(A_121))
      | ~ r2_hidden(A_1,u1_struct_0(B_120))
      | ~ m1_pre_topc(B_120,A_121)
      | ~ l1_pre_topc(A_121) ) ),
    inference(resolution,[status(thm)],[c_80,c_2])).

tff(c_121,plain,(
    ! [A_1,B_120] :
      ( ~ r2_hidden(A_1,u1_struct_0(B_120))
      | ~ m1_pre_topc(B_120,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_119,c_83])).

tff(c_125,plain,(
    ! [A_137,B_138] :
      ( ~ r2_hidden(A_137,u1_struct_0(B_138))
      | ~ m1_pre_topc(B_138,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_121])).

tff(c_128,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_125])).

tff(c_132,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_128])).

tff(c_142,plain,(
    ! [B_144,C_145] :
      ( k3_funct_2(u1_struct_0('#skF_4'),B_144,C_145,'#skF_6') = k1_funct_1(C_145,'#skF_6')
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),B_144)))
      | ~ v1_funct_2(C_145,u1_struct_0('#skF_4'),B_144)
      | ~ v1_funct_1(C_145) ) ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_145,plain,
    ( k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') = k1_funct_1('#skF_5','#skF_6')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_142])).

tff(c_148,plain,(
    k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') = k1_funct_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_145])).

tff(c_18,plain,(
    k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') != k1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_149,plain,(
    k1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k1_funct_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_18])).

tff(c_70,plain,(
    ! [C_114,A_115,B_116] :
      ( v1_relat_1(C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_74,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_70])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_36,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_42,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_94,plain,(
    ! [A_128,B_129,C_130,D_131] :
      ( k2_partfun1(A_128,B_129,C_130,D_131) = k7_relat_1(C_130,D_131)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129)))
      | ~ v1_funct_1(C_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_96,plain,(
    ! [D_131] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_131) = k7_relat_1('#skF_5',D_131)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_26,c_94])).

tff(c_99,plain,(
    ! [D_131] : k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_131) = k7_relat_1('#skF_5',D_131) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_96])).

tff(c_135,plain,(
    ! [D_141,B_143,E_139,C_142,A_140] :
      ( k3_tmap_1(A_140,B_143,C_142,D_141,E_139) = k2_partfun1(u1_struct_0(C_142),u1_struct_0(B_143),E_139,u1_struct_0(D_141))
      | ~ m1_pre_topc(D_141,C_142)
      | ~ m1_subset_1(E_139,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_142),u1_struct_0(B_143))))
      | ~ v1_funct_2(E_139,u1_struct_0(C_142),u1_struct_0(B_143))
      | ~ v1_funct_1(E_139)
      | ~ m1_pre_topc(D_141,A_140)
      | ~ m1_pre_topc(C_142,A_140)
      | ~ l1_pre_topc(B_143)
      | ~ v2_pre_topc(B_143)
      | v2_struct_0(B_143)
      | ~ l1_pre_topc(A_140)
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_137,plain,(
    ! [A_140,D_141] :
      ( k3_tmap_1(A_140,'#skF_2','#skF_4',D_141,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_141))
      | ~ m1_pre_topc(D_141,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_141,A_140)
      | ~ m1_pre_topc('#skF_4',A_140)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_140)
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140) ) ),
    inference(resolution,[status(thm)],[c_26,c_135])).

tff(c_140,plain,(
    ! [D_141,A_140] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_141)) = k3_tmap_1(A_140,'#skF_2','#skF_4',D_141,'#skF_5')
      | ~ m1_pre_topc(D_141,'#skF_4')
      | ~ m1_pre_topc(D_141,A_140)
      | ~ m1_pre_topc('#skF_4',A_140)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_140)
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_30,c_28,c_99,c_137])).

tff(c_154,plain,(
    ! [D_146,A_147] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_146)) = k3_tmap_1(A_147,'#skF_2','#skF_4',D_146,'#skF_5')
      | ~ m1_pre_topc(D_146,'#skF_4')
      | ~ m1_pre_topc(D_146,A_147)
      | ~ m1_pre_topc('#skF_4',A_147)
      | ~ l1_pre_topc(A_147)
      | ~ v2_pre_topc(A_147)
      | v2_struct_0(A_147) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_140])).

tff(c_160,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_154])).

tff(c_171,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_32,c_24,c_160])).

tff(c_172,plain,(
    k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_171])).

tff(c_4,plain,(
    ! [C_6,B_5,A_4] :
      ( k1_funct_1(k7_relat_1(C_6,B_5),A_4) = k1_funct_1(C_6,A_4)
      | ~ r2_hidden(A_4,B_5)
      | ~ v1_funct_1(C_6)
      | ~ v1_relat_1(C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_176,plain,(
    ! [A_4] :
      ( k1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),A_4) = k1_funct_1('#skF_5',A_4)
      | ~ r2_hidden(A_4,u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_4])).

tff(c_185,plain,(
    ! [A_152] :
      ( k1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),A_152) = k1_funct_1('#skF_5',A_152)
      | ~ r2_hidden(A_152,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_30,c_176])).

tff(c_188,plain,(
    k1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') = k1_funct_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_185])).

tff(c_192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_188])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:35:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.28  
% 2.42/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.28  %$ v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.42/1.28  
% 2.42/1.28  %Foreground sorts:
% 2.42/1.28  
% 2.42/1.28  
% 2.42/1.28  %Background operators:
% 2.42/1.28  
% 2.42/1.28  
% 2.42/1.28  %Foreground operators:
% 2.42/1.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.42/1.28  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.42/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.42/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.42/1.28  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.42/1.28  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.42/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.42/1.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.42/1.28  tff('#skF_6', type, '#skF_6': $i).
% 2.42/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.42/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.42/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.42/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.42/1.28  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.42/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.42/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.42/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.42/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.28  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.42/1.28  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.42/1.28  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.42/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.42/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.42/1.28  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.42/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.42/1.28  
% 2.42/1.30  tff(f_153, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (r2_hidden(F, u1_struct_0(C)) => (k3_funct_2(u1_struct_0(D), u1_struct_0(B), E, F) = k1_funct_1(k3_tmap_1(A, B, D, C, E), F)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_tmap_1)).
% 2.42/1.30  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.42/1.30  tff(f_63, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.42/1.30  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.42/1.30  tff(f_32, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.42/1.30  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.42/1.30  tff(f_50, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.42/1.30  tff(f_102, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 2.42/1.30  tff(f_40, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, B) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_funct_1)).
% 2.42/1.30  tff(c_30, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.42/1.30  tff(c_28, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.42/1.30  tff(c_26, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.42/1.30  tff(c_24, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.42/1.30  tff(c_20, plain, (r2_hidden('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.42/1.30  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.42/1.30  tff(c_32, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.42/1.30  tff(c_51, plain, (![B_112, A_113]: (l1_pre_topc(B_112) | ~m1_pre_topc(B_112, A_113) | ~l1_pre_topc(A_113))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.42/1.30  tff(c_57, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_51])).
% 2.42/1.30  tff(c_64, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_57])).
% 2.42/1.30  tff(c_22, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.42/1.30  tff(c_109, plain, (![A_133, B_134, C_135, D_136]: (k3_funct_2(A_133, B_134, C_135, D_136)=k1_funct_1(C_135, D_136) | ~m1_subset_1(D_136, A_133) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))) | ~v1_funct_2(C_135, A_133, B_134) | ~v1_funct_1(C_135) | v1_xboole_0(A_133))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.42/1.30  tff(c_118, plain, (![B_134, C_135]: (k3_funct_2(u1_struct_0('#skF_4'), B_134, C_135, '#skF_6')=k1_funct_1(C_135, '#skF_6') | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), B_134))) | ~v1_funct_2(C_135, u1_struct_0('#skF_4'), B_134) | ~v1_funct_1(C_135) | v1_xboole_0(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_22, c_109])).
% 2.42/1.30  tff(c_119, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_118])).
% 2.42/1.30  tff(c_80, plain, (![B_120, A_121]: (m1_subset_1(u1_struct_0(B_120), k1_zfmisc_1(u1_struct_0(A_121))) | ~m1_pre_topc(B_120, A_121) | ~l1_pre_topc(A_121))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.42/1.30  tff(c_2, plain, (![C_3, B_2, A_1]: (~v1_xboole_0(C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.42/1.30  tff(c_83, plain, (![A_121, A_1, B_120]: (~v1_xboole_0(u1_struct_0(A_121)) | ~r2_hidden(A_1, u1_struct_0(B_120)) | ~m1_pre_topc(B_120, A_121) | ~l1_pre_topc(A_121))), inference(resolution, [status(thm)], [c_80, c_2])).
% 2.42/1.30  tff(c_121, plain, (![A_1, B_120]: (~r2_hidden(A_1, u1_struct_0(B_120)) | ~m1_pre_topc(B_120, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_119, c_83])).
% 2.42/1.30  tff(c_125, plain, (![A_137, B_138]: (~r2_hidden(A_137, u1_struct_0(B_138)) | ~m1_pre_topc(B_138, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_121])).
% 2.42/1.30  tff(c_128, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_20, c_125])).
% 2.42/1.30  tff(c_132, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_128])).
% 2.42/1.30  tff(c_142, plain, (![B_144, C_145]: (k3_funct_2(u1_struct_0('#skF_4'), B_144, C_145, '#skF_6')=k1_funct_1(C_145, '#skF_6') | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), B_144))) | ~v1_funct_2(C_145, u1_struct_0('#skF_4'), B_144) | ~v1_funct_1(C_145))), inference(splitRight, [status(thm)], [c_118])).
% 2.42/1.30  tff(c_145, plain, (k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')=k1_funct_1('#skF_5', '#skF_6') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_26, c_142])).
% 2.42/1.30  tff(c_148, plain, (k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')=k1_funct_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_145])).
% 2.42/1.30  tff(c_18, plain, (k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')!=k1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.42/1.30  tff(c_149, plain, (k1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_18])).
% 2.42/1.30  tff(c_70, plain, (![C_114, A_115, B_116]: (v1_relat_1(C_114) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.42/1.30  tff(c_74, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_26, c_70])).
% 2.42/1.30  tff(c_50, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.42/1.30  tff(c_48, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.42/1.30  tff(c_36, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.42/1.30  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.42/1.30  tff(c_42, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.42/1.30  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.42/1.30  tff(c_94, plain, (![A_128, B_129, C_130, D_131]: (k2_partfun1(A_128, B_129, C_130, D_131)=k7_relat_1(C_130, D_131) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))) | ~v1_funct_1(C_130))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.42/1.30  tff(c_96, plain, (![D_131]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_131)=k7_relat_1('#skF_5', D_131) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_26, c_94])).
% 2.42/1.30  tff(c_99, plain, (![D_131]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_131)=k7_relat_1('#skF_5', D_131))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_96])).
% 2.42/1.30  tff(c_135, plain, (![D_141, B_143, E_139, C_142, A_140]: (k3_tmap_1(A_140, B_143, C_142, D_141, E_139)=k2_partfun1(u1_struct_0(C_142), u1_struct_0(B_143), E_139, u1_struct_0(D_141)) | ~m1_pre_topc(D_141, C_142) | ~m1_subset_1(E_139, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_142), u1_struct_0(B_143)))) | ~v1_funct_2(E_139, u1_struct_0(C_142), u1_struct_0(B_143)) | ~v1_funct_1(E_139) | ~m1_pre_topc(D_141, A_140) | ~m1_pre_topc(C_142, A_140) | ~l1_pre_topc(B_143) | ~v2_pre_topc(B_143) | v2_struct_0(B_143) | ~l1_pre_topc(A_140) | ~v2_pre_topc(A_140) | v2_struct_0(A_140))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.42/1.30  tff(c_137, plain, (![A_140, D_141]: (k3_tmap_1(A_140, '#skF_2', '#skF_4', D_141, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_141)) | ~m1_pre_topc(D_141, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_141, A_140) | ~m1_pre_topc('#skF_4', A_140) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_140) | ~v2_pre_topc(A_140) | v2_struct_0(A_140))), inference(resolution, [status(thm)], [c_26, c_135])).
% 2.42/1.30  tff(c_140, plain, (![D_141, A_140]: (k7_relat_1('#skF_5', u1_struct_0(D_141))=k3_tmap_1(A_140, '#skF_2', '#skF_4', D_141, '#skF_5') | ~m1_pre_topc(D_141, '#skF_4') | ~m1_pre_topc(D_141, A_140) | ~m1_pre_topc('#skF_4', A_140) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_140) | ~v2_pre_topc(A_140) | v2_struct_0(A_140))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_30, c_28, c_99, c_137])).
% 2.42/1.30  tff(c_154, plain, (![D_146, A_147]: (k7_relat_1('#skF_5', u1_struct_0(D_146))=k3_tmap_1(A_147, '#skF_2', '#skF_4', D_146, '#skF_5') | ~m1_pre_topc(D_146, '#skF_4') | ~m1_pre_topc(D_146, A_147) | ~m1_pre_topc('#skF_4', A_147) | ~l1_pre_topc(A_147) | ~v2_pre_topc(A_147) | v2_struct_0(A_147))), inference(negUnitSimplification, [status(thm)], [c_44, c_140])).
% 2.42/1.30  tff(c_160, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_154])).
% 2.42/1.30  tff(c_171, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_32, c_24, c_160])).
% 2.42/1.30  tff(c_172, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_50, c_171])).
% 2.42/1.30  tff(c_4, plain, (![C_6, B_5, A_4]: (k1_funct_1(k7_relat_1(C_6, B_5), A_4)=k1_funct_1(C_6, A_4) | ~r2_hidden(A_4, B_5) | ~v1_funct_1(C_6) | ~v1_relat_1(C_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.42/1.30  tff(c_176, plain, (![A_4]: (k1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), A_4)=k1_funct_1('#skF_5', A_4) | ~r2_hidden(A_4, u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_172, c_4])).
% 2.42/1.30  tff(c_185, plain, (![A_152]: (k1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), A_152)=k1_funct_1('#skF_5', A_152) | ~r2_hidden(A_152, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_30, c_176])).
% 2.42/1.30  tff(c_188, plain, (k1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')=k1_funct_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_20, c_185])).
% 2.42/1.30  tff(c_192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149, c_188])).
% 2.42/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.30  
% 2.42/1.30  Inference rules
% 2.42/1.30  ----------------------
% 2.42/1.30  #Ref     : 0
% 2.42/1.30  #Sup     : 27
% 2.42/1.30  #Fact    : 0
% 2.42/1.30  #Define  : 0
% 2.42/1.30  #Split   : 3
% 2.42/1.30  #Chain   : 0
% 2.42/1.30  #Close   : 0
% 2.42/1.30  
% 2.42/1.30  Ordering : KBO
% 2.42/1.30  
% 2.42/1.30  Simplification rules
% 2.42/1.30  ----------------------
% 2.42/1.30  #Subsume      : 1
% 2.42/1.30  #Demod        : 27
% 2.42/1.30  #Tautology    : 9
% 2.42/1.30  #SimpNegUnit  : 5
% 2.42/1.30  #BackRed      : 1
% 2.42/1.30  
% 2.42/1.30  #Partial instantiations: 0
% 2.42/1.30  #Strategies tried      : 1
% 2.42/1.30  
% 2.42/1.30  Timing (in seconds)
% 2.42/1.30  ----------------------
% 2.42/1.30  Preprocessing        : 0.34
% 2.42/1.30  Parsing              : 0.18
% 2.42/1.30  CNF conversion       : 0.03
% 2.42/1.30  Main loop            : 0.19
% 2.42/1.30  Inferencing          : 0.07
% 2.42/1.30  Reduction            : 0.06
% 2.42/1.30  Demodulation         : 0.04
% 2.42/1.30  BG Simplification    : 0.02
% 2.42/1.30  Subsumption          : 0.03
% 2.42/1.30  Abstraction          : 0.01
% 2.42/1.30  MUC search           : 0.00
% 2.42/1.30  Cooper               : 0.00
% 2.42/1.30  Total                : 0.57
% 2.42/1.30  Index Insertion      : 0.00
% 2.42/1.30  Index Deletion       : 0.00
% 2.42/1.30  Index Matching       : 0.00
% 2.42/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
