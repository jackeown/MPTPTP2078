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
% DateTime   : Thu Dec  3 10:27:13 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 162 expanded)
%              Number of leaves         :   34 (  75 expanded)
%              Depth                    :   11
%              Number of atoms          :  157 ( 701 expanded)
%              Number of equality atoms :   18 (  34 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_142,negated_conjecture,(
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

tff(f_68,axiom,(
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

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_52,axiom,(
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

tff(c_30,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_28,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_94,plain,(
    ! [A_84,B_85,D_86] :
      ( r2_funct_2(A_84,B_85,D_86,D_86)
      | ~ m1_subset_1(D_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85)))
      | ~ v1_funct_2(D_86,A_84,B_85)
      | ~ v1_funct_1(D_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_96,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_94])).

tff(c_99,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_96])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_32,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_49,plain,(
    ! [B_68,A_69] :
      ( l1_pre_topc(B_68)
      | ~ m1_pre_topc(B_68,A_69)
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_55,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_49])).

tff(c_59,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_55])).

tff(c_22,plain,(
    ! [A_53] :
      ( m1_pre_topc(A_53,A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_60,plain,(
    ! [B_70,A_71] :
      ( v1_relat_1(B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_71))
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_63,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_26,c_60])).

tff(c_66,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_63])).

tff(c_67,plain,(
    ! [C_72,A_73,B_74] :
      ( v4_relat_1(C_72,A_73)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_71,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_26,c_67])).

tff(c_77,plain,(
    ! [B_78,A_79] :
      ( k7_relat_1(B_78,A_79) = B_78
      | ~ v4_relat_1(B_78,A_79)
      | ~ v1_relat_1(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_80,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_71,c_77])).

tff(c_83,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_80])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_38,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_36,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_88,plain,(
    ! [A_80,B_81,C_82,D_83] :
      ( k2_partfun1(A_80,B_81,C_82,D_83) = k7_relat_1(C_82,D_83)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81)))
      | ~ v1_funct_1(C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_90,plain,(
    ! [D_83] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',D_83) = k7_relat_1('#skF_4',D_83)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_88])).

tff(c_93,plain,(
    ! [D_83] : k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',D_83) = k7_relat_1('#skF_4',D_83) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_90])).

tff(c_116,plain,(
    ! [D_92,C_96,E_95,B_94,A_93] :
      ( k3_tmap_1(A_93,B_94,C_96,D_92,E_95) = k2_partfun1(u1_struct_0(C_96),u1_struct_0(B_94),E_95,u1_struct_0(D_92))
      | ~ m1_pre_topc(D_92,C_96)
      | ~ m1_subset_1(E_95,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_96),u1_struct_0(B_94))))
      | ~ v1_funct_2(E_95,u1_struct_0(C_96),u1_struct_0(B_94))
      | ~ v1_funct_1(E_95)
      | ~ m1_pre_topc(D_92,A_93)
      | ~ m1_pre_topc(C_96,A_93)
      | ~ l1_pre_topc(B_94)
      | ~ v2_pre_topc(B_94)
      | v2_struct_0(B_94)
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_118,plain,(
    ! [A_93,D_92] :
      ( k3_tmap_1(A_93,'#skF_2','#skF_3',D_92,'#skF_4') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_92))
      | ~ m1_pre_topc(D_92,'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc(D_92,A_93)
      | ~ m1_pre_topc('#skF_3',A_93)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(resolution,[status(thm)],[c_26,c_116])).

tff(c_121,plain,(
    ! [D_92,A_93] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_92)) = k3_tmap_1(A_93,'#skF_2','#skF_3',D_92,'#skF_4')
      | ~ m1_pre_topc(D_92,'#skF_3')
      | ~ m1_pre_topc(D_92,A_93)
      | ~ m1_pre_topc('#skF_3',A_93)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_30,c_28,c_93,c_118])).

tff(c_123,plain,(
    ! [D_97,A_98] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_97)) = k3_tmap_1(A_98,'#skF_2','#skF_3',D_97,'#skF_4')
      | ~ m1_pre_topc(D_97,'#skF_3')
      | ~ m1_pre_topc(D_97,A_98)
      | ~ m1_pre_topc('#skF_3',A_98)
      | ~ l1_pre_topc(A_98)
      | ~ v2_pre_topc(A_98)
      | v2_struct_0(A_98) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_121])).

tff(c_127,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_123])).

tff(c_131,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_32,c_83,c_127])).

tff(c_132,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_131])).

tff(c_133,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_136,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_133])).

tff(c_140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_136])).

tff(c_141,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_24,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_155,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_24])).

tff(c_158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_155])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:24:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.25  
% 2.31/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.26  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.31/1.26  
% 2.31/1.26  %Foreground sorts:
% 2.31/1.26  
% 2.31/1.26  
% 2.31/1.26  %Background operators:
% 2.31/1.26  
% 2.31/1.26  
% 2.31/1.26  %Foreground operators:
% 2.31/1.26  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.31/1.26  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.31/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.31/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.26  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.31/1.26  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.31/1.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.31/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.31/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.31/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.31/1.26  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.31/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.31/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.31/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.31/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.31/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.26  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.31/1.26  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.31/1.26  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.31/1.26  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.31/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.31/1.26  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.31/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.31/1.26  
% 2.31/1.27  tff(f_142, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), D, k3_tmap_1(A, B, C, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tmap_1)).
% 2.31/1.27  tff(f_68, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 2.31/1.27  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.31/1.27  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 2.31/1.27  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.31/1.27  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.31/1.27  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.31/1.27  tff(f_40, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.31/1.27  tff(f_52, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.31/1.27  tff(f_107, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 2.31/1.27  tff(c_30, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.31/1.27  tff(c_28, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.31/1.27  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.31/1.27  tff(c_94, plain, (![A_84, B_85, D_86]: (r2_funct_2(A_84, B_85, D_86, D_86) | ~m1_subset_1(D_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))) | ~v1_funct_2(D_86, A_84, B_85) | ~v1_funct_1(D_86))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.31/1.27  tff(c_96, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_94])).
% 2.31/1.27  tff(c_99, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_96])).
% 2.31/1.27  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.31/1.27  tff(c_32, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.31/1.27  tff(c_49, plain, (![B_68, A_69]: (l1_pre_topc(B_68) | ~m1_pre_topc(B_68, A_69) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.31/1.27  tff(c_55, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_49])).
% 2.31/1.27  tff(c_59, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_55])).
% 2.31/1.27  tff(c_22, plain, (![A_53]: (m1_pre_topc(A_53, A_53) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.31/1.27  tff(c_46, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.31/1.27  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.31/1.27  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.31/1.27  tff(c_60, plain, (![B_70, A_71]: (v1_relat_1(B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(A_71)) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.31/1.27  tff(c_63, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_26, c_60])).
% 2.31/1.27  tff(c_66, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_63])).
% 2.31/1.27  tff(c_67, plain, (![C_72, A_73, B_74]: (v4_relat_1(C_72, A_73) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.31/1.27  tff(c_71, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_67])).
% 2.31/1.27  tff(c_77, plain, (![B_78, A_79]: (k7_relat_1(B_78, A_79)=B_78 | ~v4_relat_1(B_78, A_79) | ~v1_relat_1(B_78))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.31/1.27  tff(c_80, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_71, c_77])).
% 2.31/1.27  tff(c_83, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_80])).
% 2.31/1.27  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.31/1.27  tff(c_38, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.31/1.27  tff(c_36, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.31/1.27  tff(c_88, plain, (![A_80, B_81, C_82, D_83]: (k2_partfun1(A_80, B_81, C_82, D_83)=k7_relat_1(C_82, D_83) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))) | ~v1_funct_1(C_82))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.31/1.27  tff(c_90, plain, (![D_83]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', D_83)=k7_relat_1('#skF_4', D_83) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_88])).
% 2.31/1.27  tff(c_93, plain, (![D_83]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', D_83)=k7_relat_1('#skF_4', D_83))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_90])).
% 2.31/1.27  tff(c_116, plain, (![D_92, C_96, E_95, B_94, A_93]: (k3_tmap_1(A_93, B_94, C_96, D_92, E_95)=k2_partfun1(u1_struct_0(C_96), u1_struct_0(B_94), E_95, u1_struct_0(D_92)) | ~m1_pre_topc(D_92, C_96) | ~m1_subset_1(E_95, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_96), u1_struct_0(B_94)))) | ~v1_funct_2(E_95, u1_struct_0(C_96), u1_struct_0(B_94)) | ~v1_funct_1(E_95) | ~m1_pre_topc(D_92, A_93) | ~m1_pre_topc(C_96, A_93) | ~l1_pre_topc(B_94) | ~v2_pre_topc(B_94) | v2_struct_0(B_94) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.31/1.27  tff(c_118, plain, (![A_93, D_92]: (k3_tmap_1(A_93, '#skF_2', '#skF_3', D_92, '#skF_4')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_92)) | ~m1_pre_topc(D_92, '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc(D_92, A_93) | ~m1_pre_topc('#skF_3', A_93) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93) | v2_struct_0(A_93))), inference(resolution, [status(thm)], [c_26, c_116])).
% 2.31/1.27  tff(c_121, plain, (![D_92, A_93]: (k7_relat_1('#skF_4', u1_struct_0(D_92))=k3_tmap_1(A_93, '#skF_2', '#skF_3', D_92, '#skF_4') | ~m1_pre_topc(D_92, '#skF_3') | ~m1_pre_topc(D_92, A_93) | ~m1_pre_topc('#skF_3', A_93) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93) | v2_struct_0(A_93))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_30, c_28, c_93, c_118])).
% 2.31/1.27  tff(c_123, plain, (![D_97, A_98]: (k7_relat_1('#skF_4', u1_struct_0(D_97))=k3_tmap_1(A_98, '#skF_2', '#skF_3', D_97, '#skF_4') | ~m1_pre_topc(D_97, '#skF_3') | ~m1_pre_topc(D_97, A_98) | ~m1_pre_topc('#skF_3', A_98) | ~l1_pre_topc(A_98) | ~v2_pre_topc(A_98) | v2_struct_0(A_98))), inference(negUnitSimplification, [status(thm)], [c_40, c_121])).
% 2.31/1.27  tff(c_127, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_123])).
% 2.31/1.27  tff(c_131, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_32, c_83, c_127])).
% 2.31/1.27  tff(c_132, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_46, c_131])).
% 2.31/1.27  tff(c_133, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_132])).
% 2.31/1.27  tff(c_136, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_22, c_133])).
% 2.31/1.27  tff(c_140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_136])).
% 2.31/1.27  tff(c_141, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_132])).
% 2.31/1.27  tff(c_24, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.31/1.27  tff(c_155, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_24])).
% 2.31/1.27  tff(c_158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_155])).
% 2.31/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.27  
% 2.31/1.27  Inference rules
% 2.31/1.27  ----------------------
% 2.31/1.27  #Ref     : 0
% 2.31/1.27  #Sup     : 19
% 2.31/1.27  #Fact    : 0
% 2.31/1.27  #Define  : 0
% 2.31/1.27  #Split   : 1
% 2.31/1.27  #Chain   : 0
% 2.31/1.27  #Close   : 0
% 2.31/1.27  
% 2.31/1.27  Ordering : KBO
% 2.31/1.27  
% 2.31/1.27  Simplification rules
% 2.31/1.27  ----------------------
% 2.31/1.27  #Subsume      : 0
% 2.31/1.27  #Demod        : 26
% 2.31/1.27  #Tautology    : 7
% 2.31/1.27  #SimpNegUnit  : 3
% 2.31/1.27  #BackRed      : 1
% 2.31/1.27  
% 2.31/1.27  #Partial instantiations: 0
% 2.31/1.27  #Strategies tried      : 1
% 2.31/1.27  
% 2.31/1.27  Timing (in seconds)
% 2.31/1.27  ----------------------
% 2.31/1.27  Preprocessing        : 0.35
% 2.31/1.27  Parsing              : 0.19
% 2.31/1.27  CNF conversion       : 0.03
% 2.31/1.27  Main loop            : 0.16
% 2.31/1.27  Inferencing          : 0.06
% 2.31/1.27  Reduction            : 0.05
% 2.31/1.27  Demodulation         : 0.04
% 2.31/1.27  BG Simplification    : 0.01
% 2.31/1.27  Subsumption          : 0.03
% 2.31/1.28  Abstraction          : 0.01
% 2.31/1.28  MUC search           : 0.00
% 2.31/1.28  Cooper               : 0.00
% 2.31/1.28  Total                : 0.55
% 2.31/1.28  Index Insertion      : 0.00
% 2.31/1.28  Index Deletion       : 0.00
% 2.31/1.28  Index Matching       : 0.00
% 2.31/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
