%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:10 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 127 expanded)
%              Number of leaves         :   38 (  64 expanded)
%              Depth                    :   12
%              Number of atoms          :  182 ( 634 expanded)
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
                          & v1_funct_2(E,u1_struct_0(D),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                       => ( m1_pre_topc(C,D)
                         => ! [F] :
                              ( m1_subset_1(F,u1_struct_0(D))
                             => ( r2_hidden(F,u1_struct_0(C))
                               => k3_funct_2(u1_struct_0(D),u1_struct_0(B),E,F) = k1_funct_1(k3_tmap_1(A,B,D,C,E),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tmap_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_80,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_112,axiom,(
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

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,B)
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).

tff(c_32,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_30,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_34,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_56,plain,(
    ! [B_114,A_115] :
      ( l1_pre_topc(B_114)
      | ~ m1_pre_topc(B_114,A_115)
      | ~ l1_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_62,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_56])).

tff(c_69,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_62])).

tff(c_12,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_24,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_106,plain,(
    ! [A_126,B_127,C_128,D_129] :
      ( k3_funct_2(A_126,B_127,C_128,D_129) = k1_funct_1(C_128,D_129)
      | ~ m1_subset_1(D_129,A_126)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127)))
      | ~ v1_funct_2(C_128,A_126,B_127)
      | ~ v1_funct_1(C_128)
      | v1_xboole_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_112,plain,(
    ! [B_127,C_128] :
      ( k3_funct_2(u1_struct_0('#skF_4'),B_127,C_128,'#skF_6') = k1_funct_1(C_128,'#skF_6')
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),B_127)))
      | ~ v1_funct_2(C_128,u1_struct_0('#skF_4'),B_127)
      | ~ v1_funct_1(C_128)
      | v1_xboole_0(u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_24,c_106])).

tff(c_113,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_16,plain,(
    ! [A_21] :
      ( ~ v1_xboole_0(u1_struct_0(A_21))
      | ~ l1_struct_0(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_116,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_113,c_16])).

tff(c_119,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_116])).

tff(c_122,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_119])).

tff(c_126,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_122])).

tff(c_129,plain,(
    ! [B_130,C_131] :
      ( k3_funct_2(u1_struct_0('#skF_4'),B_130,C_131,'#skF_6') = k1_funct_1(C_131,'#skF_6')
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),B_130)))
      | ~ v1_funct_2(C_131,u1_struct_0('#skF_4'),B_130)
      | ~ v1_funct_1(C_131) ) ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_132,plain,
    ( k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') = k1_funct_1('#skF_5','#skF_6')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_129])).

tff(c_135,plain,(
    k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') = k1_funct_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_132])).

tff(c_20,plain,(
    k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') != k1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_143,plain,(
    k1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k1_funct_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_20])).

tff(c_22,plain,(
    r2_hidden('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_75,plain,(
    ! [B_116,A_117] :
      ( v1_relat_1(B_116)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(A_117))
      | ~ v1_relat_1(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_78,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_28,c_75])).

tff(c_81,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_78])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_50,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_26,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_38,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_44,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_42,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_91,plain,(
    ! [A_121,B_122,C_123,D_124] :
      ( k2_partfun1(A_121,B_122,C_123,D_124) = k7_relat_1(C_123,D_124)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122)))
      | ~ v1_funct_1(C_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_93,plain,(
    ! [D_124] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_124) = k7_relat_1('#skF_5',D_124)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_91])).

tff(c_96,plain,(
    ! [D_124] : k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_124) = k7_relat_1('#skF_5',D_124) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_93])).

tff(c_136,plain,(
    ! [C_136,A_133,D_132,E_135,B_134] :
      ( k3_tmap_1(A_133,B_134,C_136,D_132,E_135) = k2_partfun1(u1_struct_0(C_136),u1_struct_0(B_134),E_135,u1_struct_0(D_132))
      | ~ m1_pre_topc(D_132,C_136)
      | ~ m1_subset_1(E_135,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_136),u1_struct_0(B_134))))
      | ~ v1_funct_2(E_135,u1_struct_0(C_136),u1_struct_0(B_134))
      | ~ v1_funct_1(E_135)
      | ~ m1_pre_topc(D_132,A_133)
      | ~ m1_pre_topc(C_136,A_133)
      | ~ l1_pre_topc(B_134)
      | ~ v2_pre_topc(B_134)
      | v2_struct_0(B_134)
      | ~ l1_pre_topc(A_133)
      | ~ v2_pre_topc(A_133)
      | v2_struct_0(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_138,plain,(
    ! [A_133,D_132] :
      ( k3_tmap_1(A_133,'#skF_2','#skF_4',D_132,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_132))
      | ~ m1_pre_topc(D_132,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_132,A_133)
      | ~ m1_pre_topc('#skF_4',A_133)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_133)
      | ~ v2_pre_topc(A_133)
      | v2_struct_0(A_133) ) ),
    inference(resolution,[status(thm)],[c_28,c_136])).

tff(c_141,plain,(
    ! [D_132,A_133] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_132)) = k3_tmap_1(A_133,'#skF_2','#skF_4',D_132,'#skF_5')
      | ~ m1_pre_topc(D_132,'#skF_4')
      | ~ m1_pre_topc(D_132,A_133)
      | ~ m1_pre_topc('#skF_4',A_133)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_133)
      | ~ v2_pre_topc(A_133)
      | v2_struct_0(A_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_32,c_30,c_96,c_138])).

tff(c_148,plain,(
    ! [D_137,A_138] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_137)) = k3_tmap_1(A_138,'#skF_2','#skF_4',D_137,'#skF_5')
      | ~ m1_pre_topc(D_137,'#skF_4')
      | ~ m1_pre_topc(D_137,A_138)
      | ~ m1_pre_topc('#skF_4',A_138)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_141])).

tff(c_154,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_148])).

tff(c_165,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_34,c_26,c_154])).

tff(c_166,plain,(
    k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_165])).

tff(c_6,plain,(
    ! [C_8,B_7,A_6] :
      ( k1_funct_1(k7_relat_1(C_8,B_7),A_6) = k1_funct_1(C_8,A_6)
      | ~ r2_hidden(A_6,B_7)
      | ~ v1_funct_1(C_8)
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_170,plain,(
    ! [A_6] :
      ( k1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),A_6) = k1_funct_1('#skF_5',A_6)
      | ~ r2_hidden(A_6,u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_6])).

tff(c_178,plain,(
    ! [A_139] :
      ( k1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),A_139) = k1_funct_1('#skF_5',A_139)
      | ~ r2_hidden(A_139,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_32,c_170])).

tff(c_181,plain,(
    k1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') = k1_funct_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_178])).

tff(c_185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_181])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:30:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.37  
% 2.52/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.37  %$ v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.52/1.37  
% 2.52/1.37  %Foreground sorts:
% 2.52/1.37  
% 2.52/1.37  
% 2.52/1.37  %Background operators:
% 2.52/1.37  
% 2.52/1.37  
% 2.52/1.37  %Foreground operators:
% 2.52/1.37  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.52/1.37  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.52/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.52/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.52/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.52/1.37  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.52/1.37  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.52/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.52/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.52/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.52/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.52/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.52/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.52/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.52/1.37  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.52/1.37  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.52/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.52/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.52/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.52/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.52/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.52/1.37  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.52/1.37  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.52/1.37  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.52/1.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.52/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.52/1.37  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.52/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.52/1.37  
% 2.52/1.39  tff(f_156, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (r2_hidden(F, u1_struct_0(C)) => (k3_funct_2(u1_struct_0(D), u1_struct_0(B), E, F) = k1_funct_1(k3_tmap_1(A, B, D, C, E), F)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_tmap_1)).
% 2.52/1.39  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.52/1.39  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.52/1.39  tff(f_61, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.52/1.39  tff(f_80, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.52/1.39  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.52/1.39  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.52/1.39  tff(f_48, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.52/1.39  tff(f_112, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 2.52/1.39  tff(f_42, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, B) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_funct_1)).
% 2.52/1.39  tff(c_32, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.52/1.39  tff(c_30, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.52/1.39  tff(c_28, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.52/1.39  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.52/1.39  tff(c_34, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.52/1.39  tff(c_56, plain, (![B_114, A_115]: (l1_pre_topc(B_114) | ~m1_pre_topc(B_114, A_115) | ~l1_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.52/1.39  tff(c_62, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_56])).
% 2.52/1.39  tff(c_69, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_62])).
% 2.52/1.39  tff(c_12, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.52/1.39  tff(c_36, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.52/1.39  tff(c_24, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.52/1.39  tff(c_106, plain, (![A_126, B_127, C_128, D_129]: (k3_funct_2(A_126, B_127, C_128, D_129)=k1_funct_1(C_128, D_129) | ~m1_subset_1(D_129, A_126) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))) | ~v1_funct_2(C_128, A_126, B_127) | ~v1_funct_1(C_128) | v1_xboole_0(A_126))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.52/1.39  tff(c_112, plain, (![B_127, C_128]: (k3_funct_2(u1_struct_0('#skF_4'), B_127, C_128, '#skF_6')=k1_funct_1(C_128, '#skF_6') | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), B_127))) | ~v1_funct_2(C_128, u1_struct_0('#skF_4'), B_127) | ~v1_funct_1(C_128) | v1_xboole_0(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_24, c_106])).
% 2.52/1.39  tff(c_113, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_112])).
% 2.52/1.39  tff(c_16, plain, (![A_21]: (~v1_xboole_0(u1_struct_0(A_21)) | ~l1_struct_0(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.52/1.39  tff(c_116, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_113, c_16])).
% 2.52/1.39  tff(c_119, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_36, c_116])).
% 2.52/1.39  tff(c_122, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_12, c_119])).
% 2.52/1.39  tff(c_126, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69, c_122])).
% 2.52/1.39  tff(c_129, plain, (![B_130, C_131]: (k3_funct_2(u1_struct_0('#skF_4'), B_130, C_131, '#skF_6')=k1_funct_1(C_131, '#skF_6') | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), B_130))) | ~v1_funct_2(C_131, u1_struct_0('#skF_4'), B_130) | ~v1_funct_1(C_131))), inference(splitRight, [status(thm)], [c_112])).
% 2.52/1.39  tff(c_132, plain, (k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')=k1_funct_1('#skF_5', '#skF_6') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_129])).
% 2.52/1.39  tff(c_135, plain, (k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')=k1_funct_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_132])).
% 2.52/1.39  tff(c_20, plain, (k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')!=k1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.52/1.39  tff(c_143, plain, (k1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_20])).
% 2.52/1.39  tff(c_22, plain, (r2_hidden('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.52/1.39  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.52/1.39  tff(c_75, plain, (![B_116, A_117]: (v1_relat_1(B_116) | ~m1_subset_1(B_116, k1_zfmisc_1(A_117)) | ~v1_relat_1(A_117))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.52/1.39  tff(c_78, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_28, c_75])).
% 2.52/1.39  tff(c_81, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_78])).
% 2.52/1.39  tff(c_52, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.52/1.39  tff(c_50, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.52/1.39  tff(c_26, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.52/1.39  tff(c_38, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.52/1.39  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.52/1.39  tff(c_44, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.52/1.39  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.52/1.39  tff(c_91, plain, (![A_121, B_122, C_123, D_124]: (k2_partfun1(A_121, B_122, C_123, D_124)=k7_relat_1(C_123, D_124) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))) | ~v1_funct_1(C_123))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.52/1.39  tff(c_93, plain, (![D_124]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_124)=k7_relat_1('#skF_5', D_124) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_28, c_91])).
% 2.52/1.39  tff(c_96, plain, (![D_124]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_124)=k7_relat_1('#skF_5', D_124))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_93])).
% 2.52/1.39  tff(c_136, plain, (![C_136, A_133, D_132, E_135, B_134]: (k3_tmap_1(A_133, B_134, C_136, D_132, E_135)=k2_partfun1(u1_struct_0(C_136), u1_struct_0(B_134), E_135, u1_struct_0(D_132)) | ~m1_pre_topc(D_132, C_136) | ~m1_subset_1(E_135, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_136), u1_struct_0(B_134)))) | ~v1_funct_2(E_135, u1_struct_0(C_136), u1_struct_0(B_134)) | ~v1_funct_1(E_135) | ~m1_pre_topc(D_132, A_133) | ~m1_pre_topc(C_136, A_133) | ~l1_pre_topc(B_134) | ~v2_pre_topc(B_134) | v2_struct_0(B_134) | ~l1_pre_topc(A_133) | ~v2_pre_topc(A_133) | v2_struct_0(A_133))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.52/1.39  tff(c_138, plain, (![A_133, D_132]: (k3_tmap_1(A_133, '#skF_2', '#skF_4', D_132, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_132)) | ~m1_pre_topc(D_132, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_132, A_133) | ~m1_pre_topc('#skF_4', A_133) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_133) | ~v2_pre_topc(A_133) | v2_struct_0(A_133))), inference(resolution, [status(thm)], [c_28, c_136])).
% 2.52/1.39  tff(c_141, plain, (![D_132, A_133]: (k7_relat_1('#skF_5', u1_struct_0(D_132))=k3_tmap_1(A_133, '#skF_2', '#skF_4', D_132, '#skF_5') | ~m1_pre_topc(D_132, '#skF_4') | ~m1_pre_topc(D_132, A_133) | ~m1_pre_topc('#skF_4', A_133) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_133) | ~v2_pre_topc(A_133) | v2_struct_0(A_133))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_32, c_30, c_96, c_138])).
% 2.52/1.39  tff(c_148, plain, (![D_137, A_138]: (k7_relat_1('#skF_5', u1_struct_0(D_137))=k3_tmap_1(A_138, '#skF_2', '#skF_4', D_137, '#skF_5') | ~m1_pre_topc(D_137, '#skF_4') | ~m1_pre_topc(D_137, A_138) | ~m1_pre_topc('#skF_4', A_138) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(negUnitSimplification, [status(thm)], [c_46, c_141])).
% 2.52/1.39  tff(c_154, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_148])).
% 2.52/1.39  tff(c_165, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_34, c_26, c_154])).
% 2.52/1.39  tff(c_166, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_52, c_165])).
% 2.52/1.39  tff(c_6, plain, (![C_8, B_7, A_6]: (k1_funct_1(k7_relat_1(C_8, B_7), A_6)=k1_funct_1(C_8, A_6) | ~r2_hidden(A_6, B_7) | ~v1_funct_1(C_8) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.52/1.39  tff(c_170, plain, (![A_6]: (k1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), A_6)=k1_funct_1('#skF_5', A_6) | ~r2_hidden(A_6, u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_166, c_6])).
% 2.52/1.39  tff(c_178, plain, (![A_139]: (k1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), A_139)=k1_funct_1('#skF_5', A_139) | ~r2_hidden(A_139, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_32, c_170])).
% 2.52/1.39  tff(c_181, plain, (k1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')=k1_funct_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_22, c_178])).
% 2.52/1.39  tff(c_185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_143, c_181])).
% 2.52/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.39  
% 2.52/1.39  Inference rules
% 2.52/1.39  ----------------------
% 2.52/1.39  #Ref     : 0
% 2.52/1.39  #Sup     : 24
% 2.52/1.39  #Fact    : 0
% 2.52/1.39  #Define  : 0
% 2.52/1.39  #Split   : 2
% 2.52/1.39  #Chain   : 0
% 2.52/1.39  #Close   : 0
% 2.52/1.39  
% 2.52/1.39  Ordering : KBO
% 2.52/1.39  
% 2.52/1.39  Simplification rules
% 2.52/1.39  ----------------------
% 2.52/1.39  #Subsume      : 1
% 2.52/1.39  #Demod        : 27
% 2.52/1.39  #Tautology    : 9
% 2.52/1.39  #SimpNegUnit  : 6
% 2.52/1.39  #BackRed      : 1
% 2.52/1.39  
% 2.52/1.39  #Partial instantiations: 0
% 2.52/1.39  #Strategies tried      : 1
% 2.52/1.39  
% 2.52/1.39  Timing (in seconds)
% 2.52/1.39  ----------------------
% 2.52/1.39  Preprocessing        : 0.39
% 2.52/1.39  Parsing              : 0.20
% 2.52/1.39  CNF conversion       : 0.04
% 2.52/1.39  Main loop            : 0.20
% 2.52/1.39  Inferencing          : 0.07
% 2.52/1.39  Reduction            : 0.07
% 2.52/1.39  Demodulation         : 0.05
% 2.52/1.39  BG Simplification    : 0.02
% 2.52/1.39  Subsumption          : 0.03
% 2.52/1.39  Abstraction          : 0.02
% 2.52/1.39  MUC search           : 0.00
% 2.52/1.39  Cooper               : 0.00
% 2.52/1.39  Total                : 0.63
% 2.52/1.39  Index Insertion      : 0.00
% 2.52/1.39  Index Deletion       : 0.00
% 2.52/1.40  Index Matching       : 0.00
% 2.52/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
