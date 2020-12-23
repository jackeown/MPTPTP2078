%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:10 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 129 expanded)
%              Number of leaves         :   37 (  64 expanded)
%              Depth                    :   12
%              Number of atoms          :  189 ( 660 expanded)
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

tff(f_158,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_tmap_1)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_114,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_41,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,B)
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_funct_1)).

tff(c_32,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_30,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_26,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_22,plain,(
    r2_hidden('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_34,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_54,plain,(
    ! [B_116,A_117] :
      ( l1_pre_topc(B_116)
      | ~ m1_pre_topc(B_116,A_117)
      | ~ l1_pre_topc(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_60,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_54])).

tff(c_67,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_60])).

tff(c_24,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_119,plain,(
    ! [A_138,B_139,C_140,D_141] :
      ( k3_funct_2(A_138,B_139,C_140,D_141) = k1_funct_1(C_140,D_141)
      | ~ m1_subset_1(D_141,A_138)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139)))
      | ~ v1_funct_2(C_140,A_138,B_139)
      | ~ v1_funct_1(C_140)
      | v1_xboole_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_128,plain,(
    ! [B_139,C_140] :
      ( k3_funct_2(u1_struct_0('#skF_4'),B_139,C_140,'#skF_6') = k1_funct_1(C_140,'#skF_6')
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),B_139)))
      | ~ v1_funct_2(C_140,u1_struct_0('#skF_4'),B_139)
      | ~ v1_funct_1(C_140)
      | v1_xboole_0(u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_24,c_119])).

tff(c_129,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_85,plain,(
    ! [B_123,A_124] :
      ( m1_subset_1(u1_struct_0(B_123),k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ m1_pre_topc(B_123,A_124)
      | ~ l1_pre_topc(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2,plain,(
    ! [C_3,B_2,A_1] :
      ( ~ v1_xboole_0(C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_91,plain,(
    ! [A_124,A_1,B_123] :
      ( ~ v1_xboole_0(u1_struct_0(A_124))
      | ~ r2_hidden(A_1,u1_struct_0(B_123))
      | ~ m1_pre_topc(B_123,A_124)
      | ~ l1_pre_topc(A_124) ) ),
    inference(resolution,[status(thm)],[c_85,c_2])).

tff(c_138,plain,(
    ! [A_1,B_123] :
      ( ~ r2_hidden(A_1,u1_struct_0(B_123))
      | ~ m1_pre_topc(B_123,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_129,c_91])).

tff(c_142,plain,(
    ! [A_147,B_148] :
      ( ~ r2_hidden(A_147,u1_struct_0(B_148))
      | ~ m1_pre_topc(B_148,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_138])).

tff(c_145,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_142])).

tff(c_149,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_145])).

tff(c_153,plain,(
    ! [B_149,C_150] :
      ( k3_funct_2(u1_struct_0('#skF_4'),B_149,C_150,'#skF_6') = k1_funct_1(C_150,'#skF_6')
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),B_149)))
      | ~ v1_funct_2(C_150,u1_struct_0('#skF_4'),B_149)
      | ~ v1_funct_1(C_150) ) ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_156,plain,
    ( k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') = k1_funct_1('#skF_5','#skF_6')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_153])).

tff(c_159,plain,(
    k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') = k1_funct_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_156])).

tff(c_20,plain,(
    k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') != k1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_160,plain,(
    k1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k1_funct_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_20])).

tff(c_6,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_73,plain,(
    ! [B_118,A_119] :
      ( v1_relat_1(B_118)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(A_119))
      | ~ v1_relat_1(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_76,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_28,c_73])).

tff(c_79,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_76])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_50,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_38,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_44,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_42,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_104,plain,(
    ! [A_133,B_134,C_135,D_136] :
      ( k2_partfun1(A_133,B_134,C_135,D_136) = k7_relat_1(C_135,D_136)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134)))
      | ~ v1_funct_1(C_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_106,plain,(
    ! [D_136] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_136) = k7_relat_1('#skF_5',D_136)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_104])).

tff(c_109,plain,(
    ! [D_136] : k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_136) = k7_relat_1('#skF_5',D_136) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_106])).

tff(c_166,plain,(
    ! [C_158,E_155,A_159,D_156,B_157] :
      ( k3_tmap_1(A_159,B_157,C_158,D_156,E_155) = k2_partfun1(u1_struct_0(C_158),u1_struct_0(B_157),E_155,u1_struct_0(D_156))
      | ~ m1_pre_topc(D_156,C_158)
      | ~ m1_subset_1(E_155,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_158),u1_struct_0(B_157))))
      | ~ v1_funct_2(E_155,u1_struct_0(C_158),u1_struct_0(B_157))
      | ~ v1_funct_1(E_155)
      | ~ m1_pre_topc(D_156,A_159)
      | ~ m1_pre_topc(C_158,A_159)
      | ~ l1_pre_topc(B_157)
      | ~ v2_pre_topc(B_157)
      | v2_struct_0(B_157)
      | ~ l1_pre_topc(A_159)
      | ~ v2_pre_topc(A_159)
      | v2_struct_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_168,plain,(
    ! [A_159,D_156] :
      ( k3_tmap_1(A_159,'#skF_2','#skF_4',D_156,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_156))
      | ~ m1_pre_topc(D_156,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_156,A_159)
      | ~ m1_pre_topc('#skF_4',A_159)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_159)
      | ~ v2_pre_topc(A_159)
      | v2_struct_0(A_159) ) ),
    inference(resolution,[status(thm)],[c_28,c_166])).

tff(c_171,plain,(
    ! [D_156,A_159] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_156)) = k3_tmap_1(A_159,'#skF_2','#skF_4',D_156,'#skF_5')
      | ~ m1_pre_topc(D_156,'#skF_4')
      | ~ m1_pre_topc(D_156,A_159)
      | ~ m1_pre_topc('#skF_4',A_159)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_159)
      | ~ v2_pre_topc(A_159)
      | v2_struct_0(A_159) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_32,c_30,c_109,c_168])).

tff(c_173,plain,(
    ! [D_160,A_161] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_160)) = k3_tmap_1(A_161,'#skF_2','#skF_4',D_160,'#skF_5')
      | ~ m1_pre_topc(D_160,'#skF_4')
      | ~ m1_pre_topc(D_160,A_161)
      | ~ m1_pre_topc('#skF_4',A_161)
      | ~ l1_pre_topc(A_161)
      | ~ v2_pre_topc(A_161)
      | v2_struct_0(A_161) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_171])).

tff(c_179,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_173])).

tff(c_190,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_34,c_26,c_179])).

tff(c_191,plain,(
    k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_190])).

tff(c_8,plain,(
    ! [C_11,B_10,A_9] :
      ( k1_funct_1(k7_relat_1(C_11,B_10),A_9) = k1_funct_1(C_11,A_9)
      | ~ r2_hidden(A_9,B_10)
      | ~ v1_funct_1(C_11)
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_195,plain,(
    ! [A_9] :
      ( k1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),A_9) = k1_funct_1('#skF_5',A_9)
      | ~ r2_hidden(A_9,u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_8])).

tff(c_204,plain,(
    ! [A_162] :
      ( k1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),A_162) = k1_funct_1('#skF_5',A_162)
      | ~ r2_hidden(A_162,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_32,c_195])).

tff(c_207,plain,(
    k1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') = k1_funct_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_204])).

tff(c_211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_207])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:29:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.47  
% 2.73/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.47  %$ v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.73/1.47  
% 2.73/1.47  %Foreground sorts:
% 2.73/1.47  
% 2.73/1.47  
% 2.73/1.47  %Background operators:
% 2.73/1.47  
% 2.73/1.47  
% 2.73/1.47  %Foreground operators:
% 2.73/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.73/1.47  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.73/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.73/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.47  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.73/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.73/1.47  tff('#skF_5', type, '#skF_5': $i).
% 2.73/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.73/1.47  tff('#skF_6', type, '#skF_6': $i).
% 2.73/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.73/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.73/1.47  tff('#skF_1', type, '#skF_1': $i).
% 2.73/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.73/1.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.73/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.73/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.73/1.47  tff('#skF_4', type, '#skF_4': $i).
% 2.73/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.47  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.73/1.47  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.73/1.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.73/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.73/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.73/1.47  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.73/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.73/1.47  
% 2.84/1.49  tff(f_158, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (r2_hidden(F, u1_struct_0(C)) => (k3_funct_2(u1_struct_0(D), u1_struct_0(B), E, F) = k1_funct_1(k3_tmap_1(A, B, D, C, E), F)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_tmap_1)).
% 2.84/1.49  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.84/1.49  tff(f_68, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.84/1.49  tff(f_114, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.84/1.49  tff(f_32, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.84/1.49  tff(f_41, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.84/1.49  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.84/1.49  tff(f_55, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.84/1.49  tff(f_107, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 2.84/1.49  tff(f_49, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, B) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_funct_1)).
% 2.84/1.49  tff(c_32, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.84/1.49  tff(c_30, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.84/1.49  tff(c_28, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.84/1.49  tff(c_26, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.84/1.49  tff(c_22, plain, (r2_hidden('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.84/1.49  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.84/1.49  tff(c_34, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.84/1.49  tff(c_54, plain, (![B_116, A_117]: (l1_pre_topc(B_116) | ~m1_pre_topc(B_116, A_117) | ~l1_pre_topc(A_117))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.84/1.49  tff(c_60, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_54])).
% 2.84/1.49  tff(c_67, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_60])).
% 2.84/1.49  tff(c_24, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.84/1.49  tff(c_119, plain, (![A_138, B_139, C_140, D_141]: (k3_funct_2(A_138, B_139, C_140, D_141)=k1_funct_1(C_140, D_141) | ~m1_subset_1(D_141, A_138) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))) | ~v1_funct_2(C_140, A_138, B_139) | ~v1_funct_1(C_140) | v1_xboole_0(A_138))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.84/1.49  tff(c_128, plain, (![B_139, C_140]: (k3_funct_2(u1_struct_0('#skF_4'), B_139, C_140, '#skF_6')=k1_funct_1(C_140, '#skF_6') | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), B_139))) | ~v1_funct_2(C_140, u1_struct_0('#skF_4'), B_139) | ~v1_funct_1(C_140) | v1_xboole_0(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_24, c_119])).
% 2.84/1.49  tff(c_129, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_128])).
% 2.84/1.49  tff(c_85, plain, (![B_123, A_124]: (m1_subset_1(u1_struct_0(B_123), k1_zfmisc_1(u1_struct_0(A_124))) | ~m1_pre_topc(B_123, A_124) | ~l1_pre_topc(A_124))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.84/1.49  tff(c_2, plain, (![C_3, B_2, A_1]: (~v1_xboole_0(C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.84/1.49  tff(c_91, plain, (![A_124, A_1, B_123]: (~v1_xboole_0(u1_struct_0(A_124)) | ~r2_hidden(A_1, u1_struct_0(B_123)) | ~m1_pre_topc(B_123, A_124) | ~l1_pre_topc(A_124))), inference(resolution, [status(thm)], [c_85, c_2])).
% 2.84/1.49  tff(c_138, plain, (![A_1, B_123]: (~r2_hidden(A_1, u1_struct_0(B_123)) | ~m1_pre_topc(B_123, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_129, c_91])).
% 2.84/1.49  tff(c_142, plain, (![A_147, B_148]: (~r2_hidden(A_147, u1_struct_0(B_148)) | ~m1_pre_topc(B_148, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_138])).
% 2.84/1.49  tff(c_145, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_22, c_142])).
% 2.84/1.49  tff(c_149, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_145])).
% 2.84/1.49  tff(c_153, plain, (![B_149, C_150]: (k3_funct_2(u1_struct_0('#skF_4'), B_149, C_150, '#skF_6')=k1_funct_1(C_150, '#skF_6') | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), B_149))) | ~v1_funct_2(C_150, u1_struct_0('#skF_4'), B_149) | ~v1_funct_1(C_150))), inference(splitRight, [status(thm)], [c_128])).
% 2.84/1.49  tff(c_156, plain, (k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')=k1_funct_1('#skF_5', '#skF_6') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_153])).
% 2.84/1.49  tff(c_159, plain, (k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')=k1_funct_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_156])).
% 2.84/1.49  tff(c_20, plain, (k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')!=k1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.84/1.49  tff(c_160, plain, (k1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_20])).
% 2.84/1.49  tff(c_6, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.84/1.49  tff(c_73, plain, (![B_118, A_119]: (v1_relat_1(B_118) | ~m1_subset_1(B_118, k1_zfmisc_1(A_119)) | ~v1_relat_1(A_119))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.84/1.49  tff(c_76, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_28, c_73])).
% 2.84/1.49  tff(c_79, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_76])).
% 2.84/1.49  tff(c_52, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.84/1.49  tff(c_50, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.84/1.49  tff(c_38, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.84/1.49  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.84/1.49  tff(c_44, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.84/1.49  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.84/1.49  tff(c_104, plain, (![A_133, B_134, C_135, D_136]: (k2_partfun1(A_133, B_134, C_135, D_136)=k7_relat_1(C_135, D_136) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))) | ~v1_funct_1(C_135))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.84/1.49  tff(c_106, plain, (![D_136]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_136)=k7_relat_1('#skF_5', D_136) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_28, c_104])).
% 2.84/1.49  tff(c_109, plain, (![D_136]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_136)=k7_relat_1('#skF_5', D_136))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_106])).
% 2.84/1.49  tff(c_166, plain, (![C_158, E_155, A_159, D_156, B_157]: (k3_tmap_1(A_159, B_157, C_158, D_156, E_155)=k2_partfun1(u1_struct_0(C_158), u1_struct_0(B_157), E_155, u1_struct_0(D_156)) | ~m1_pre_topc(D_156, C_158) | ~m1_subset_1(E_155, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_158), u1_struct_0(B_157)))) | ~v1_funct_2(E_155, u1_struct_0(C_158), u1_struct_0(B_157)) | ~v1_funct_1(E_155) | ~m1_pre_topc(D_156, A_159) | ~m1_pre_topc(C_158, A_159) | ~l1_pre_topc(B_157) | ~v2_pre_topc(B_157) | v2_struct_0(B_157) | ~l1_pre_topc(A_159) | ~v2_pre_topc(A_159) | v2_struct_0(A_159))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.84/1.49  tff(c_168, plain, (![A_159, D_156]: (k3_tmap_1(A_159, '#skF_2', '#skF_4', D_156, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_156)) | ~m1_pre_topc(D_156, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_156, A_159) | ~m1_pre_topc('#skF_4', A_159) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_159) | ~v2_pre_topc(A_159) | v2_struct_0(A_159))), inference(resolution, [status(thm)], [c_28, c_166])).
% 2.84/1.49  tff(c_171, plain, (![D_156, A_159]: (k7_relat_1('#skF_5', u1_struct_0(D_156))=k3_tmap_1(A_159, '#skF_2', '#skF_4', D_156, '#skF_5') | ~m1_pre_topc(D_156, '#skF_4') | ~m1_pre_topc(D_156, A_159) | ~m1_pre_topc('#skF_4', A_159) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_159) | ~v2_pre_topc(A_159) | v2_struct_0(A_159))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_32, c_30, c_109, c_168])).
% 2.84/1.49  tff(c_173, plain, (![D_160, A_161]: (k7_relat_1('#skF_5', u1_struct_0(D_160))=k3_tmap_1(A_161, '#skF_2', '#skF_4', D_160, '#skF_5') | ~m1_pre_topc(D_160, '#skF_4') | ~m1_pre_topc(D_160, A_161) | ~m1_pre_topc('#skF_4', A_161) | ~l1_pre_topc(A_161) | ~v2_pre_topc(A_161) | v2_struct_0(A_161))), inference(negUnitSimplification, [status(thm)], [c_46, c_171])).
% 2.84/1.49  tff(c_179, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_173])).
% 2.84/1.49  tff(c_190, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_34, c_26, c_179])).
% 2.84/1.49  tff(c_191, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_52, c_190])).
% 2.84/1.49  tff(c_8, plain, (![C_11, B_10, A_9]: (k1_funct_1(k7_relat_1(C_11, B_10), A_9)=k1_funct_1(C_11, A_9) | ~r2_hidden(A_9, B_10) | ~v1_funct_1(C_11) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.84/1.49  tff(c_195, plain, (![A_9]: (k1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), A_9)=k1_funct_1('#skF_5', A_9) | ~r2_hidden(A_9, u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_191, c_8])).
% 2.84/1.49  tff(c_204, plain, (![A_162]: (k1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), A_162)=k1_funct_1('#skF_5', A_162) | ~r2_hidden(A_162, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_32, c_195])).
% 2.84/1.49  tff(c_207, plain, (k1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')=k1_funct_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_22, c_204])).
% 2.84/1.49  tff(c_211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_160, c_207])).
% 2.84/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.49  
% 2.84/1.49  Inference rules
% 2.84/1.49  ----------------------
% 2.84/1.49  #Ref     : 0
% 2.84/1.49  #Sup     : 29
% 2.84/1.49  #Fact    : 0
% 2.84/1.49  #Define  : 0
% 2.84/1.49  #Split   : 5
% 2.84/1.49  #Chain   : 0
% 2.84/1.49  #Close   : 0
% 2.84/1.49  
% 2.84/1.49  Ordering : KBO
% 2.84/1.49  
% 2.84/1.49  Simplification rules
% 2.84/1.49  ----------------------
% 2.84/1.49  #Subsume      : 0
% 2.84/1.49  #Demod        : 33
% 2.84/1.49  #Tautology    : 9
% 2.84/1.49  #SimpNegUnit  : 6
% 2.84/1.49  #BackRed      : 1
% 2.84/1.49  
% 2.84/1.49  #Partial instantiations: 0
% 2.84/1.49  #Strategies tried      : 1
% 2.84/1.49  
% 2.84/1.49  Timing (in seconds)
% 2.84/1.49  ----------------------
% 2.84/1.50  Preprocessing        : 0.43
% 2.84/1.50  Parsing              : 0.23
% 2.84/1.50  CNF conversion       : 0.04
% 2.84/1.50  Main loop            : 0.21
% 2.84/1.50  Inferencing          : 0.08
% 2.84/1.50  Reduction            : 0.07
% 2.84/1.50  Demodulation         : 0.05
% 2.84/1.50  BG Simplification    : 0.02
% 2.84/1.50  Subsumption          : 0.03
% 2.84/1.50  Abstraction          : 0.01
% 2.84/1.50  MUC search           : 0.00
% 2.84/1.50  Cooper               : 0.00
% 2.84/1.50  Total                : 0.69
% 2.84/1.50  Index Insertion      : 0.00
% 2.84/1.50  Index Deletion       : 0.00
% 2.84/1.50  Index Matching       : 0.00
% 2.84/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
