%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:09 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 129 expanded)
%              Number of leaves         :   37 (  64 expanded)
%              Depth                    :   12
%              Number of atoms          :  188 ( 659 expanded)
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

tff(f_37,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

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

tff(f_45,axiom,(
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

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_34,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_58,plain,(
    ! [B_116,A_117] :
      ( l1_pre_topc(B_116)
      | ~ m1_pre_topc(B_116,A_117)
      | ~ l1_pre_topc(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_64,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_58])).

tff(c_71,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_64])).

tff(c_24,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_118,plain,(
    ! [A_135,B_136,C_137,D_138] :
      ( k3_funct_2(A_135,B_136,C_137,D_138) = k1_funct_1(C_137,D_138)
      | ~ m1_subset_1(D_138,A_135)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136)))
      | ~ v1_funct_2(C_137,A_135,B_136)
      | ~ v1_funct_1(C_137)
      | v1_xboole_0(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_127,plain,(
    ! [B_136,C_137] :
      ( k3_funct_2(u1_struct_0('#skF_4'),B_136,C_137,'#skF_6') = k1_funct_1(C_137,'#skF_6')
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),B_136)))
      | ~ v1_funct_2(C_137,u1_struct_0('#skF_4'),B_136)
      | ~ v1_funct_1(C_137)
      | v1_xboole_0(u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_24,c_118])).

tff(c_128,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_87,plain,(
    ! [B_123,A_124] :
      ( m1_subset_1(u1_struct_0(B_123),k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ m1_pre_topc(B_123,A_124)
      | ~ l1_pre_topc(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_4,plain,(
    ! [B_5,A_3] :
      ( v1_xboole_0(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_91,plain,(
    ! [B_123,A_124] :
      ( v1_xboole_0(u1_struct_0(B_123))
      | ~ v1_xboole_0(u1_struct_0(A_124))
      | ~ m1_pre_topc(B_123,A_124)
      | ~ l1_pre_topc(A_124) ) ),
    inference(resolution,[status(thm)],[c_87,c_4])).

tff(c_137,plain,(
    ! [B_123] :
      ( v1_xboole_0(u1_struct_0(B_123))
      | ~ m1_pre_topc(B_123,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_128,c_91])).

tff(c_141,plain,(
    ! [B_144] :
      ( v1_xboole_0(u1_struct_0(B_144))
      | ~ m1_pre_topc(B_144,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_137])).

tff(c_22,plain,(
    r2_hidden('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_53,plain,(
    ! [B_114,A_115] :
      ( ~ v1_xboole_0(B_114)
      | ~ r2_hidden(A_115,B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_57,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_53])).

tff(c_146,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_141,c_57])).

tff(c_151,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_146])).

tff(c_155,plain,(
    ! [B_145,C_146] :
      ( k3_funct_2(u1_struct_0('#skF_4'),B_145,C_146,'#skF_6') = k1_funct_1(C_146,'#skF_6')
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),B_145)))
      | ~ v1_funct_2(C_146,u1_struct_0('#skF_4'),B_145)
      | ~ v1_funct_1(C_146) ) ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_158,plain,
    ( k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') = k1_funct_1('#skF_5','#skF_6')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_155])).

tff(c_161,plain,(
    k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') = k1_funct_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_158])).

tff(c_20,plain,(
    k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_6') != k1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_162,plain,(
    k1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') != k1_funct_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_20])).

tff(c_77,plain,(
    ! [C_118,A_119,B_120] :
      ( v1_relat_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_81,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_77])).

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

tff(c_103,plain,(
    ! [A_130,B_131,C_132,D_133] :
      ( k2_partfun1(A_130,B_131,C_132,D_133) = k7_relat_1(C_132,D_133)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131)))
      | ~ v1_funct_1(C_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_105,plain,(
    ! [D_133] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_133) = k7_relat_1('#skF_5',D_133)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_103])).

tff(c_108,plain,(
    ! [D_133] : k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_133) = k7_relat_1('#skF_5',D_133) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_105])).

tff(c_168,plain,(
    ! [C_154,E_151,A_155,B_153,D_152] :
      ( k3_tmap_1(A_155,B_153,C_154,D_152,E_151) = k2_partfun1(u1_struct_0(C_154),u1_struct_0(B_153),E_151,u1_struct_0(D_152))
      | ~ m1_pre_topc(D_152,C_154)
      | ~ m1_subset_1(E_151,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_154),u1_struct_0(B_153))))
      | ~ v1_funct_2(E_151,u1_struct_0(C_154),u1_struct_0(B_153))
      | ~ v1_funct_1(E_151)
      | ~ m1_pre_topc(D_152,A_155)
      | ~ m1_pre_topc(C_154,A_155)
      | ~ l1_pre_topc(B_153)
      | ~ v2_pre_topc(B_153)
      | v2_struct_0(B_153)
      | ~ l1_pre_topc(A_155)
      | ~ v2_pre_topc(A_155)
      | v2_struct_0(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_170,plain,(
    ! [A_155,D_152] :
      ( k3_tmap_1(A_155,'#skF_2','#skF_4',D_152,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_152))
      | ~ m1_pre_topc(D_152,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_152,A_155)
      | ~ m1_pre_topc('#skF_4',A_155)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_155)
      | ~ v2_pre_topc(A_155)
      | v2_struct_0(A_155) ) ),
    inference(resolution,[status(thm)],[c_28,c_168])).

tff(c_173,plain,(
    ! [D_152,A_155] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_152)) = k3_tmap_1(A_155,'#skF_2','#skF_4',D_152,'#skF_5')
      | ~ m1_pre_topc(D_152,'#skF_4')
      | ~ m1_pre_topc(D_152,A_155)
      | ~ m1_pre_topc('#skF_4',A_155)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_155)
      | ~ v2_pre_topc(A_155)
      | v2_struct_0(A_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_32,c_30,c_108,c_170])).

tff(c_175,plain,(
    ! [D_156,A_157] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_156)) = k3_tmap_1(A_157,'#skF_2','#skF_4',D_156,'#skF_5')
      | ~ m1_pre_topc(D_156,'#skF_4')
      | ~ m1_pre_topc(D_156,A_157)
      | ~ m1_pre_topc('#skF_4',A_157)
      | ~ l1_pre_topc(A_157)
      | ~ v2_pre_topc(A_157)
      | v2_struct_0(A_157) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_173])).

tff(c_181,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_175])).

tff(c_192,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_34,c_26,c_181])).

tff(c_193,plain,(
    k7_relat_1('#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_192])).

tff(c_6,plain,(
    ! [C_8,B_7,A_6] :
      ( k1_funct_1(k7_relat_1(C_8,B_7),A_6) = k1_funct_1(C_8,A_6)
      | ~ r2_hidden(A_6,B_7)
      | ~ v1_funct_1(C_8)
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_197,plain,(
    ! [A_6] :
      ( k1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),A_6) = k1_funct_1('#skF_5',A_6)
      | ~ r2_hidden(A_6,u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_6])).

tff(c_206,plain,(
    ! [A_158] :
      ( k1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),A_158) = k1_funct_1('#skF_5',A_158)
      | ~ r2_hidden(A_158,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_32,c_197])).

tff(c_209,plain,(
    k1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') = k1_funct_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_206])).

tff(c_213,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_209])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:46:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.40  
% 2.47/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.40  %$ v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.47/1.40  
% 2.47/1.40  %Foreground sorts:
% 2.47/1.40  
% 2.47/1.40  
% 2.47/1.40  %Background operators:
% 2.47/1.40  
% 2.47/1.40  
% 2.47/1.40  %Foreground operators:
% 2.47/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.47/1.40  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.47/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.47/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.40  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.47/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.47/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.47/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.47/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.47/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.47/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.47/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.47/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.47/1.40  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.47/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.47/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.47/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.47/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.40  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.47/1.40  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.47/1.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.47/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.47/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.47/1.40  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.47/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.47/1.40  
% 2.75/1.42  tff(f_158, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (r2_hidden(F, u1_struct_0(C)) => (k3_funct_2(u1_struct_0(D), u1_struct_0(B), E, F) = k1_funct_1(k3_tmap_1(A, B, D, C, E), F)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_tmap_1)).
% 2.75/1.42  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.75/1.42  tff(f_68, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.75/1.42  tff(f_114, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.75/1.42  tff(f_37, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.75/1.42  tff(f_30, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_boole)).
% 2.75/1.42  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.75/1.42  tff(f_55, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.75/1.42  tff(f_107, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 2.75/1.42  tff(f_45, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, B) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_funct_1)).
% 2.75/1.42  tff(c_32, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.75/1.42  tff(c_30, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.75/1.42  tff(c_28, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.75/1.42  tff(c_26, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.75/1.42  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.75/1.42  tff(c_34, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.75/1.42  tff(c_58, plain, (![B_116, A_117]: (l1_pre_topc(B_116) | ~m1_pre_topc(B_116, A_117) | ~l1_pre_topc(A_117))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.75/1.42  tff(c_64, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_58])).
% 2.75/1.42  tff(c_71, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_64])).
% 2.75/1.42  tff(c_24, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.75/1.42  tff(c_118, plain, (![A_135, B_136, C_137, D_138]: (k3_funct_2(A_135, B_136, C_137, D_138)=k1_funct_1(C_137, D_138) | ~m1_subset_1(D_138, A_135) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))) | ~v1_funct_2(C_137, A_135, B_136) | ~v1_funct_1(C_137) | v1_xboole_0(A_135))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.75/1.42  tff(c_127, plain, (![B_136, C_137]: (k3_funct_2(u1_struct_0('#skF_4'), B_136, C_137, '#skF_6')=k1_funct_1(C_137, '#skF_6') | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), B_136))) | ~v1_funct_2(C_137, u1_struct_0('#skF_4'), B_136) | ~v1_funct_1(C_137) | v1_xboole_0(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_24, c_118])).
% 2.75/1.42  tff(c_128, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_127])).
% 2.75/1.42  tff(c_87, plain, (![B_123, A_124]: (m1_subset_1(u1_struct_0(B_123), k1_zfmisc_1(u1_struct_0(A_124))) | ~m1_pre_topc(B_123, A_124) | ~l1_pre_topc(A_124))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.75/1.42  tff(c_4, plain, (![B_5, A_3]: (v1_xboole_0(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.75/1.42  tff(c_91, plain, (![B_123, A_124]: (v1_xboole_0(u1_struct_0(B_123)) | ~v1_xboole_0(u1_struct_0(A_124)) | ~m1_pre_topc(B_123, A_124) | ~l1_pre_topc(A_124))), inference(resolution, [status(thm)], [c_87, c_4])).
% 2.75/1.42  tff(c_137, plain, (![B_123]: (v1_xboole_0(u1_struct_0(B_123)) | ~m1_pre_topc(B_123, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_128, c_91])).
% 2.75/1.42  tff(c_141, plain, (![B_144]: (v1_xboole_0(u1_struct_0(B_144)) | ~m1_pre_topc(B_144, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_137])).
% 2.75/1.42  tff(c_22, plain, (r2_hidden('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.75/1.42  tff(c_53, plain, (![B_114, A_115]: (~v1_xboole_0(B_114) | ~r2_hidden(A_115, B_114))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.75/1.42  tff(c_57, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_53])).
% 2.75/1.42  tff(c_146, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_141, c_57])).
% 2.75/1.42  tff(c_151, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_146])).
% 2.75/1.42  tff(c_155, plain, (![B_145, C_146]: (k3_funct_2(u1_struct_0('#skF_4'), B_145, C_146, '#skF_6')=k1_funct_1(C_146, '#skF_6') | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), B_145))) | ~v1_funct_2(C_146, u1_struct_0('#skF_4'), B_145) | ~v1_funct_1(C_146))), inference(splitRight, [status(thm)], [c_127])).
% 2.75/1.42  tff(c_158, plain, (k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')=k1_funct_1('#skF_5', '#skF_6') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_155])).
% 2.75/1.42  tff(c_161, plain, (k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')=k1_funct_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_158])).
% 2.75/1.42  tff(c_20, plain, (k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_6')!=k1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.75/1.42  tff(c_162, plain, (k1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_161, c_20])).
% 2.75/1.42  tff(c_77, plain, (![C_118, A_119, B_120]: (v1_relat_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.75/1.42  tff(c_81, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_77])).
% 2.75/1.42  tff(c_52, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.75/1.42  tff(c_50, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.75/1.42  tff(c_38, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.75/1.42  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.75/1.42  tff(c_44, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.75/1.42  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.75/1.42  tff(c_103, plain, (![A_130, B_131, C_132, D_133]: (k2_partfun1(A_130, B_131, C_132, D_133)=k7_relat_1(C_132, D_133) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))) | ~v1_funct_1(C_132))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.75/1.42  tff(c_105, plain, (![D_133]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_133)=k7_relat_1('#skF_5', D_133) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_28, c_103])).
% 2.75/1.42  tff(c_108, plain, (![D_133]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_133)=k7_relat_1('#skF_5', D_133))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_105])).
% 2.75/1.42  tff(c_168, plain, (![C_154, E_151, A_155, B_153, D_152]: (k3_tmap_1(A_155, B_153, C_154, D_152, E_151)=k2_partfun1(u1_struct_0(C_154), u1_struct_0(B_153), E_151, u1_struct_0(D_152)) | ~m1_pre_topc(D_152, C_154) | ~m1_subset_1(E_151, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_154), u1_struct_0(B_153)))) | ~v1_funct_2(E_151, u1_struct_0(C_154), u1_struct_0(B_153)) | ~v1_funct_1(E_151) | ~m1_pre_topc(D_152, A_155) | ~m1_pre_topc(C_154, A_155) | ~l1_pre_topc(B_153) | ~v2_pre_topc(B_153) | v2_struct_0(B_153) | ~l1_pre_topc(A_155) | ~v2_pre_topc(A_155) | v2_struct_0(A_155))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.75/1.42  tff(c_170, plain, (![A_155, D_152]: (k3_tmap_1(A_155, '#skF_2', '#skF_4', D_152, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_152)) | ~m1_pre_topc(D_152, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_152, A_155) | ~m1_pre_topc('#skF_4', A_155) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_155) | ~v2_pre_topc(A_155) | v2_struct_0(A_155))), inference(resolution, [status(thm)], [c_28, c_168])).
% 2.75/1.42  tff(c_173, plain, (![D_152, A_155]: (k7_relat_1('#skF_5', u1_struct_0(D_152))=k3_tmap_1(A_155, '#skF_2', '#skF_4', D_152, '#skF_5') | ~m1_pre_topc(D_152, '#skF_4') | ~m1_pre_topc(D_152, A_155) | ~m1_pre_topc('#skF_4', A_155) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_155) | ~v2_pre_topc(A_155) | v2_struct_0(A_155))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_32, c_30, c_108, c_170])).
% 2.75/1.42  tff(c_175, plain, (![D_156, A_157]: (k7_relat_1('#skF_5', u1_struct_0(D_156))=k3_tmap_1(A_157, '#skF_2', '#skF_4', D_156, '#skF_5') | ~m1_pre_topc(D_156, '#skF_4') | ~m1_pre_topc(D_156, A_157) | ~m1_pre_topc('#skF_4', A_157) | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157) | v2_struct_0(A_157))), inference(negUnitSimplification, [status(thm)], [c_46, c_173])).
% 2.75/1.42  tff(c_181, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_175])).
% 2.75/1.42  tff(c_192, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_34, c_26, c_181])).
% 2.75/1.42  tff(c_193, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_52, c_192])).
% 2.75/1.42  tff(c_6, plain, (![C_8, B_7, A_6]: (k1_funct_1(k7_relat_1(C_8, B_7), A_6)=k1_funct_1(C_8, A_6) | ~r2_hidden(A_6, B_7) | ~v1_funct_1(C_8) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.75/1.42  tff(c_197, plain, (![A_6]: (k1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), A_6)=k1_funct_1('#skF_5', A_6) | ~r2_hidden(A_6, u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_193, c_6])).
% 2.75/1.42  tff(c_206, plain, (![A_158]: (k1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), A_158)=k1_funct_1('#skF_5', A_158) | ~r2_hidden(A_158, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_32, c_197])).
% 2.75/1.42  tff(c_209, plain, (k1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')=k1_funct_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_22, c_206])).
% 2.75/1.42  tff(c_213, plain, $false, inference(negUnitSimplification, [status(thm)], [c_162, c_209])).
% 2.75/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.42  
% 2.75/1.42  Inference rules
% 2.75/1.42  ----------------------
% 2.75/1.42  #Ref     : 0
% 2.75/1.42  #Sup     : 30
% 2.75/1.42  #Fact    : 0
% 2.75/1.42  #Define  : 0
% 2.75/1.42  #Split   : 5
% 2.75/1.42  #Chain   : 0
% 2.75/1.42  #Close   : 0
% 2.75/1.42  
% 2.75/1.42  Ordering : KBO
% 2.75/1.42  
% 2.75/1.42  Simplification rules
% 2.75/1.42  ----------------------
% 2.75/1.42  #Subsume      : 0
% 2.75/1.42  #Demod        : 32
% 2.75/1.42  #Tautology    : 9
% 2.75/1.42  #SimpNegUnit  : 6
% 2.75/1.42  #BackRed      : 1
% 2.75/1.42  
% 2.75/1.42  #Partial instantiations: 0
% 2.75/1.42  #Strategies tried      : 1
% 2.75/1.42  
% 2.75/1.42  Timing (in seconds)
% 2.75/1.42  ----------------------
% 2.75/1.43  Preprocessing        : 0.39
% 2.75/1.43  Parsing              : 0.20
% 2.75/1.43  CNF conversion       : 0.04
% 2.75/1.43  Main loop            : 0.21
% 2.75/1.43  Inferencing          : 0.08
% 2.75/1.43  Reduction            : 0.07
% 2.75/1.43  Demodulation         : 0.05
% 2.75/1.43  BG Simplification    : 0.02
% 2.75/1.43  Subsumption          : 0.03
% 2.75/1.43  Abstraction          : 0.01
% 2.75/1.43  MUC search           : 0.00
% 2.75/1.43  Cooper               : 0.00
% 2.75/1.43  Total                : 0.64
% 2.75/1.43  Index Insertion      : 0.00
% 2.75/1.43  Index Deletion       : 0.00
% 2.75/1.43  Index Matching       : 0.00
% 2.75/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
