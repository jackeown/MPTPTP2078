%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:11 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 108 expanded)
%              Number of leaves         :   36 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :  165 ( 428 expanded)
%              Number of equality atoms :   19 (  19 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_152,negated_conjecture,(
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
                      & v1_funct_2(D,u1_struct_0(C),u1_struct_0(B))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                   => r2_funct_2(u1_struct_0(C),u1_struct_0(B),D,k3_tmap_1(A,B,C,C,D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tmap_1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_121,axiom,(
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

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_59,axiom,(
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

tff(c_38,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_36,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_143,plain,(
    ! [A_97,B_98,D_99] :
      ( r2_funct_2(A_97,B_98,D_99,D_99)
      | ~ m1_subset_1(D_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98)))
      | ~ v1_funct_2(D_99,A_97,B_98)
      | ~ v1_funct_1(D_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_145,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_143])).

tff(c_148,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_145])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_52,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_40,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_176,plain,(
    ! [B_108,C_109,A_110] :
      ( m1_pre_topc(B_108,C_109)
      | ~ r1_tarski(u1_struct_0(B_108),u1_struct_0(C_109))
      | ~ m1_pre_topc(C_109,A_110)
      | ~ m1_pre_topc(B_108,A_110)
      | ~ l1_pre_topc(A_110)
      | ~ v2_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_184,plain,(
    ! [B_111,A_112] :
      ( m1_pre_topc(B_111,B_111)
      | ~ m1_pre_topc(B_111,A_112)
      | ~ l1_pre_topc(A_112)
      | ~ v2_pre_topc(A_112) ) ),
    inference(resolution,[status(thm)],[c_6,c_176])).

tff(c_186,plain,
    ( m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_184])).

tff(c_189,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_186])).

tff(c_14,plain,(
    ! [C_9,A_7,B_8] :
      ( v1_relat_1(C_9)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_61,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_14])).

tff(c_73,plain,(
    ! [C_78,A_79,B_80] :
      ( v4_relat_1(C_78,A_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_77,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_73])).

tff(c_10,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k1_relat_1(B_4),A_3)
      | ~ v4_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_94,plain,(
    ! [B_87,A_88] :
      ( k7_relat_1(B_87,A_88) = B_87
      | ~ r1_tarski(k1_relat_1(B_87),A_88)
      | ~ v1_relat_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_119,plain,(
    ! [B_94,A_95] :
      ( k7_relat_1(B_94,A_95) = B_94
      | ~ v4_relat_1(B_94,A_95)
      | ~ v1_relat_1(B_94) ) ),
    inference(resolution,[status(thm)],[c_10,c_94])).

tff(c_125,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_77,c_119])).

tff(c_129,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_125])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_46,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_113,plain,(
    ! [A_90,B_91,C_92,D_93] :
      ( k2_partfun1(A_90,B_91,C_92,D_93) = k7_relat_1(C_92,D_93)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91)))
      | ~ v1_funct_1(C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_115,plain,(
    ! [D_93] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',D_93) = k7_relat_1('#skF_4',D_93)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_113])).

tff(c_118,plain,(
    ! [D_93] : k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',D_93) = k7_relat_1('#skF_4',D_93) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_115])).

tff(c_222,plain,(
    ! [C_121,B_122,A_119,D_120,E_118] :
      ( k3_tmap_1(A_119,B_122,C_121,D_120,E_118) = k2_partfun1(u1_struct_0(C_121),u1_struct_0(B_122),E_118,u1_struct_0(D_120))
      | ~ m1_pre_topc(D_120,C_121)
      | ~ m1_subset_1(E_118,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_121),u1_struct_0(B_122))))
      | ~ v1_funct_2(E_118,u1_struct_0(C_121),u1_struct_0(B_122))
      | ~ v1_funct_1(E_118)
      | ~ m1_pre_topc(D_120,A_119)
      | ~ m1_pre_topc(C_121,A_119)
      | ~ l1_pre_topc(B_122)
      | ~ v2_pre_topc(B_122)
      | v2_struct_0(B_122)
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119)
      | v2_struct_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_224,plain,(
    ! [A_119,D_120] :
      ( k3_tmap_1(A_119,'#skF_2','#skF_3',D_120,'#skF_4') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_120))
      | ~ m1_pre_topc(D_120,'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc(D_120,A_119)
      | ~ m1_pre_topc('#skF_3',A_119)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119)
      | v2_struct_0(A_119) ) ),
    inference(resolution,[status(thm)],[c_34,c_222])).

tff(c_227,plain,(
    ! [D_120,A_119] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_120)) = k3_tmap_1(A_119,'#skF_2','#skF_3',D_120,'#skF_4')
      | ~ m1_pre_topc(D_120,'#skF_3')
      | ~ m1_pre_topc(D_120,A_119)
      | ~ m1_pre_topc('#skF_3',A_119)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119)
      | v2_struct_0(A_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_38,c_36,c_118,c_224])).

tff(c_229,plain,(
    ! [D_123,A_124] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_123)) = k3_tmap_1(A_124,'#skF_2','#skF_3',D_123,'#skF_4')
      | ~ m1_pre_topc(D_123,'#skF_3')
      | ~ m1_pre_topc(D_123,A_124)
      | ~ m1_pre_topc('#skF_3',A_124)
      | ~ l1_pre_topc(A_124)
      | ~ v2_pre_topc(A_124)
      | v2_struct_0(A_124) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_227])).

tff(c_233,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_229])).

tff(c_240,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_40,c_189,c_129,c_233])).

tff(c_241,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_240])).

tff(c_32,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_242,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_32])).

tff(c_245,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_242])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:46:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.32  
% 2.25/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.32  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.58/1.32  
% 2.58/1.32  %Foreground sorts:
% 2.58/1.32  
% 2.58/1.32  
% 2.58/1.32  %Background operators:
% 2.58/1.32  
% 2.58/1.32  
% 2.58/1.32  %Foreground operators:
% 2.58/1.32  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.58/1.32  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.58/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.58/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.32  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.58/1.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.58/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.58/1.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.58/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.58/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.58/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.58/1.32  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.58/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.58/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.58/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.58/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.58/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.32  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.58/1.32  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.58/1.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.58/1.32  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.58/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.58/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.58/1.32  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.58/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.58/1.32  
% 2.58/1.34  tff(f_152, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), D, k3_tmap_1(A, B, C, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tmap_1)).
% 2.58/1.34  tff(f_75, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 2.58/1.34  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.58/1.34  tff(f_121, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 2.58/1.34  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.58/1.34  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.58/1.34  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.58/1.34  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 2.58/1.34  tff(f_59, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.58/1.34  tff(f_107, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 2.58/1.34  tff(c_38, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.58/1.34  tff(c_36, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.58/1.34  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.58/1.34  tff(c_143, plain, (![A_97, B_98, D_99]: (r2_funct_2(A_97, B_98, D_99, D_99) | ~m1_subset_1(D_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))) | ~v1_funct_2(D_99, A_97, B_98) | ~v1_funct_1(D_99))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.58/1.34  tff(c_145, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_143])).
% 2.58/1.34  tff(c_148, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_145])).
% 2.58/1.34  tff(c_54, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.58/1.34  tff(c_52, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.58/1.34  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.58/1.34  tff(c_40, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.58/1.34  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.58/1.34  tff(c_176, plain, (![B_108, C_109, A_110]: (m1_pre_topc(B_108, C_109) | ~r1_tarski(u1_struct_0(B_108), u1_struct_0(C_109)) | ~m1_pre_topc(C_109, A_110) | ~m1_pre_topc(B_108, A_110) | ~l1_pre_topc(A_110) | ~v2_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.58/1.34  tff(c_184, plain, (![B_111, A_112]: (m1_pre_topc(B_111, B_111) | ~m1_pre_topc(B_111, A_112) | ~l1_pre_topc(A_112) | ~v2_pre_topc(A_112))), inference(resolution, [status(thm)], [c_6, c_176])).
% 2.58/1.34  tff(c_186, plain, (m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_184])).
% 2.58/1.34  tff(c_189, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_186])).
% 2.58/1.34  tff(c_14, plain, (![C_9, A_7, B_8]: (v1_relat_1(C_9) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.58/1.34  tff(c_61, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_14])).
% 2.58/1.34  tff(c_73, plain, (![C_78, A_79, B_80]: (v4_relat_1(C_78, A_79) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.58/1.34  tff(c_77, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_73])).
% 2.58/1.34  tff(c_10, plain, (![B_4, A_3]: (r1_tarski(k1_relat_1(B_4), A_3) | ~v4_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.58/1.34  tff(c_94, plain, (![B_87, A_88]: (k7_relat_1(B_87, A_88)=B_87 | ~r1_tarski(k1_relat_1(B_87), A_88) | ~v1_relat_1(B_87))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.58/1.34  tff(c_119, plain, (![B_94, A_95]: (k7_relat_1(B_94, A_95)=B_94 | ~v4_relat_1(B_94, A_95) | ~v1_relat_1(B_94))), inference(resolution, [status(thm)], [c_10, c_94])).
% 2.58/1.34  tff(c_125, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_77, c_119])).
% 2.58/1.34  tff(c_129, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_61, c_125])).
% 2.58/1.34  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.58/1.34  tff(c_46, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.58/1.34  tff(c_44, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.58/1.34  tff(c_113, plain, (![A_90, B_91, C_92, D_93]: (k2_partfun1(A_90, B_91, C_92, D_93)=k7_relat_1(C_92, D_93) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))) | ~v1_funct_1(C_92))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.58/1.34  tff(c_115, plain, (![D_93]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', D_93)=k7_relat_1('#skF_4', D_93) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_113])).
% 2.58/1.34  tff(c_118, plain, (![D_93]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', D_93)=k7_relat_1('#skF_4', D_93))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_115])).
% 2.58/1.34  tff(c_222, plain, (![C_121, B_122, A_119, D_120, E_118]: (k3_tmap_1(A_119, B_122, C_121, D_120, E_118)=k2_partfun1(u1_struct_0(C_121), u1_struct_0(B_122), E_118, u1_struct_0(D_120)) | ~m1_pre_topc(D_120, C_121) | ~m1_subset_1(E_118, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_121), u1_struct_0(B_122)))) | ~v1_funct_2(E_118, u1_struct_0(C_121), u1_struct_0(B_122)) | ~v1_funct_1(E_118) | ~m1_pre_topc(D_120, A_119) | ~m1_pre_topc(C_121, A_119) | ~l1_pre_topc(B_122) | ~v2_pre_topc(B_122) | v2_struct_0(B_122) | ~l1_pre_topc(A_119) | ~v2_pre_topc(A_119) | v2_struct_0(A_119))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.58/1.34  tff(c_224, plain, (![A_119, D_120]: (k3_tmap_1(A_119, '#skF_2', '#skF_3', D_120, '#skF_4')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_120)) | ~m1_pre_topc(D_120, '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc(D_120, A_119) | ~m1_pre_topc('#skF_3', A_119) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_119) | ~v2_pre_topc(A_119) | v2_struct_0(A_119))), inference(resolution, [status(thm)], [c_34, c_222])).
% 2.58/1.34  tff(c_227, plain, (![D_120, A_119]: (k7_relat_1('#skF_4', u1_struct_0(D_120))=k3_tmap_1(A_119, '#skF_2', '#skF_3', D_120, '#skF_4') | ~m1_pre_topc(D_120, '#skF_3') | ~m1_pre_topc(D_120, A_119) | ~m1_pre_topc('#skF_3', A_119) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_119) | ~v2_pre_topc(A_119) | v2_struct_0(A_119))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_38, c_36, c_118, c_224])).
% 2.58/1.34  tff(c_229, plain, (![D_123, A_124]: (k7_relat_1('#skF_4', u1_struct_0(D_123))=k3_tmap_1(A_124, '#skF_2', '#skF_3', D_123, '#skF_4') | ~m1_pre_topc(D_123, '#skF_3') | ~m1_pre_topc(D_123, A_124) | ~m1_pre_topc('#skF_3', A_124) | ~l1_pre_topc(A_124) | ~v2_pre_topc(A_124) | v2_struct_0(A_124))), inference(negUnitSimplification, [status(thm)], [c_48, c_227])).
% 2.58/1.34  tff(c_233, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_229])).
% 2.58/1.34  tff(c_240, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_40, c_189, c_129, c_233])).
% 2.58/1.34  tff(c_241, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_54, c_240])).
% 2.58/1.34  tff(c_32, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.58/1.34  tff(c_242, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_241, c_32])).
% 2.58/1.34  tff(c_245, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_148, c_242])).
% 2.58/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.34  
% 2.58/1.34  Inference rules
% 2.58/1.34  ----------------------
% 2.58/1.34  #Ref     : 0
% 2.58/1.34  #Sup     : 35
% 2.58/1.34  #Fact    : 0
% 2.58/1.34  #Define  : 0
% 2.58/1.34  #Split   : 1
% 2.58/1.34  #Chain   : 0
% 2.58/1.34  #Close   : 0
% 2.58/1.34  
% 2.58/1.34  Ordering : KBO
% 2.58/1.34  
% 2.58/1.34  Simplification rules
% 2.58/1.34  ----------------------
% 2.58/1.34  #Subsume      : 2
% 2.58/1.34  #Demod        : 32
% 2.58/1.34  #Tautology    : 16
% 2.58/1.34  #SimpNegUnit  : 3
% 2.58/1.34  #BackRed      : 1
% 2.58/1.34  
% 2.58/1.34  #Partial instantiations: 0
% 2.58/1.34  #Strategies tried      : 1
% 2.58/1.34  
% 2.58/1.34  Timing (in seconds)
% 2.58/1.34  ----------------------
% 2.58/1.34  Preprocessing        : 0.36
% 2.58/1.34  Parsing              : 0.19
% 2.58/1.34  CNF conversion       : 0.03
% 2.58/1.34  Main loop            : 0.21
% 2.58/1.34  Inferencing          : 0.07
% 2.58/1.34  Reduction            : 0.06
% 2.58/1.34  Demodulation         : 0.05
% 2.58/1.34  BG Simplification    : 0.02
% 2.58/1.34  Subsumption          : 0.04
% 2.58/1.34  Abstraction          : 0.01
% 2.58/1.34  MUC search           : 0.00
% 2.58/1.34  Cooper               : 0.00
% 2.58/1.34  Total                : 0.60
% 2.58/1.34  Index Insertion      : 0.00
% 2.58/1.34  Index Deletion       : 0.00
% 2.58/1.34  Index Matching       : 0.00
% 2.58/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
