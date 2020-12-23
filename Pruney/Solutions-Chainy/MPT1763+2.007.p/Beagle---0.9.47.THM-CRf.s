%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:11 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 104 expanded)
%              Number of leaves         :   34 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :  156 ( 419 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_146,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tmap_1)).

tff(f_69,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_115,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_101,axiom,(
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

tff(c_34,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_32,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_101,plain,(
    ! [A_87,B_88,D_89] :
      ( r2_funct_2(A_87,B_88,D_89,D_89)
      | ~ m1_subset_1(D_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88)))
      | ~ v1_funct_2(D_89,A_87,B_88)
      | ~ v1_funct_1(D_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_103,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_101])).

tff(c_106,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_103])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_36,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_134,plain,(
    ! [B_95,C_96,A_97] :
      ( m1_pre_topc(B_95,C_96)
      | ~ r1_tarski(u1_struct_0(B_95),u1_struct_0(C_96))
      | ~ m1_pre_topc(C_96,A_97)
      | ~ m1_pre_topc(B_95,A_97)
      | ~ l1_pre_topc(A_97)
      | ~ v2_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_142,plain,(
    ! [B_98,A_99] :
      ( m1_pre_topc(B_98,B_98)
      | ~ m1_pre_topc(B_98,A_99)
      | ~ l1_pre_topc(A_99)
      | ~ v2_pre_topc(A_99) ) ),
    inference(resolution,[status(thm)],[c_6,c_134])).

tff(c_144,plain,
    ( m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_142])).

tff(c_147,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_144])).

tff(c_60,plain,(
    ! [C_71,A_72,B_73] :
      ( v1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_64,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_60])).

tff(c_71,plain,(
    ! [C_79,A_80,B_81] :
      ( v4_relat_1(C_79,A_80)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_75,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_71])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k7_relat_1(B_4,A_3) = B_4
      | ~ v4_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_78,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_75,c_8])).

tff(c_81,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_78])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_42,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_86,plain,(
    ! [A_82,B_83,C_84,D_85] :
      ( k2_partfun1(A_82,B_83,C_84,D_85) = k7_relat_1(C_84,D_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83)))
      | ~ v1_funct_1(C_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_88,plain,(
    ! [D_85] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',D_85) = k7_relat_1('#skF_4',D_85)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_86])).

tff(c_91,plain,(
    ! [D_85] : k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',D_85) = k7_relat_1('#skF_4',D_85) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_88])).

tff(c_163,plain,(
    ! [E_108,B_107,C_104,A_106,D_105] :
      ( k3_tmap_1(A_106,B_107,C_104,D_105,E_108) = k2_partfun1(u1_struct_0(C_104),u1_struct_0(B_107),E_108,u1_struct_0(D_105))
      | ~ m1_pre_topc(D_105,C_104)
      | ~ m1_subset_1(E_108,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_104),u1_struct_0(B_107))))
      | ~ v1_funct_2(E_108,u1_struct_0(C_104),u1_struct_0(B_107))
      | ~ v1_funct_1(E_108)
      | ~ m1_pre_topc(D_105,A_106)
      | ~ m1_pre_topc(C_104,A_106)
      | ~ l1_pre_topc(B_107)
      | ~ v2_pre_topc(B_107)
      | v2_struct_0(B_107)
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_165,plain,(
    ! [A_106,D_105] :
      ( k3_tmap_1(A_106,'#skF_2','#skF_3',D_105,'#skF_4') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_105))
      | ~ m1_pre_topc(D_105,'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc(D_105,A_106)
      | ~ m1_pre_topc('#skF_3',A_106)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106)
      | v2_struct_0(A_106) ) ),
    inference(resolution,[status(thm)],[c_30,c_163])).

tff(c_168,plain,(
    ! [D_105,A_106] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_105)) = k3_tmap_1(A_106,'#skF_2','#skF_3',D_105,'#skF_4')
      | ~ m1_pre_topc(D_105,'#skF_3')
      | ~ m1_pre_topc(D_105,A_106)
      | ~ m1_pre_topc('#skF_3',A_106)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106)
      | v2_struct_0(A_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_34,c_32,c_91,c_165])).

tff(c_170,plain,(
    ! [D_109,A_110] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_109)) = k3_tmap_1(A_110,'#skF_2','#skF_3',D_109,'#skF_4')
      | ~ m1_pre_topc(D_109,'#skF_3')
      | ~ m1_pre_topc(D_109,A_110)
      | ~ m1_pre_topc('#skF_3',A_110)
      | ~ l1_pre_topc(A_110)
      | ~ v2_pre_topc(A_110)
      | v2_struct_0(A_110) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_168])).

tff(c_174,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_170])).

tff(c_181,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_36,c_147,c_81,c_174])).

tff(c_182,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_181])).

tff(c_28,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_183,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_28])).

tff(c_186,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_183])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:44:38 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.25  
% 2.28/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.25  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.28/1.25  
% 2.28/1.25  %Foreground sorts:
% 2.28/1.25  
% 2.28/1.25  
% 2.28/1.25  %Background operators:
% 2.28/1.25  
% 2.28/1.25  
% 2.28/1.25  %Foreground operators:
% 2.28/1.25  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.28/1.25  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.28/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.28/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.25  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.28/1.25  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.28/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.25  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.28/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.28/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.28/1.25  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.28/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.28/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.28/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.28/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.28/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.25  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.28/1.25  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.28/1.25  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.28/1.25  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.28/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.28/1.25  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.28/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.28/1.25  
% 2.28/1.26  tff(f_146, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), D, k3_tmap_1(A, B, C, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tmap_1)).
% 2.28/1.26  tff(f_69, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 2.28/1.26  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.28/1.26  tff(f_115, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 2.28/1.26  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.28/1.26  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.28/1.26  tff(f_37, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.28/1.26  tff(f_53, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.28/1.26  tff(f_101, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 2.28/1.26  tff(c_34, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.28/1.26  tff(c_32, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.28/1.26  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.28/1.26  tff(c_101, plain, (![A_87, B_88, D_89]: (r2_funct_2(A_87, B_88, D_89, D_89) | ~m1_subset_1(D_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))) | ~v1_funct_2(D_89, A_87, B_88) | ~v1_funct_1(D_89))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.28/1.26  tff(c_103, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_101])).
% 2.28/1.26  tff(c_106, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_103])).
% 2.28/1.26  tff(c_50, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.28/1.26  tff(c_48, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.28/1.26  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.28/1.26  tff(c_36, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.28/1.26  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.28/1.26  tff(c_134, plain, (![B_95, C_96, A_97]: (m1_pre_topc(B_95, C_96) | ~r1_tarski(u1_struct_0(B_95), u1_struct_0(C_96)) | ~m1_pre_topc(C_96, A_97) | ~m1_pre_topc(B_95, A_97) | ~l1_pre_topc(A_97) | ~v2_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.28/1.26  tff(c_142, plain, (![B_98, A_99]: (m1_pre_topc(B_98, B_98) | ~m1_pre_topc(B_98, A_99) | ~l1_pre_topc(A_99) | ~v2_pre_topc(A_99))), inference(resolution, [status(thm)], [c_6, c_134])).
% 2.28/1.26  tff(c_144, plain, (m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_142])).
% 2.28/1.26  tff(c_147, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_144])).
% 2.28/1.26  tff(c_60, plain, (![C_71, A_72, B_73]: (v1_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.28/1.26  tff(c_64, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_60])).
% 2.28/1.26  tff(c_71, plain, (![C_79, A_80, B_81]: (v4_relat_1(C_79, A_80) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.28/1.26  tff(c_75, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_71])).
% 2.28/1.26  tff(c_8, plain, (![B_4, A_3]: (k7_relat_1(B_4, A_3)=B_4 | ~v4_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.28/1.26  tff(c_78, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_75, c_8])).
% 2.28/1.26  tff(c_81, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_78])).
% 2.28/1.26  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.28/1.26  tff(c_42, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.28/1.26  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.28/1.26  tff(c_86, plain, (![A_82, B_83, C_84, D_85]: (k2_partfun1(A_82, B_83, C_84, D_85)=k7_relat_1(C_84, D_85) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))) | ~v1_funct_1(C_84))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.28/1.26  tff(c_88, plain, (![D_85]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', D_85)=k7_relat_1('#skF_4', D_85) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_86])).
% 2.28/1.26  tff(c_91, plain, (![D_85]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', D_85)=k7_relat_1('#skF_4', D_85))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_88])).
% 2.28/1.26  tff(c_163, plain, (![E_108, B_107, C_104, A_106, D_105]: (k3_tmap_1(A_106, B_107, C_104, D_105, E_108)=k2_partfun1(u1_struct_0(C_104), u1_struct_0(B_107), E_108, u1_struct_0(D_105)) | ~m1_pre_topc(D_105, C_104) | ~m1_subset_1(E_108, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_104), u1_struct_0(B_107)))) | ~v1_funct_2(E_108, u1_struct_0(C_104), u1_struct_0(B_107)) | ~v1_funct_1(E_108) | ~m1_pre_topc(D_105, A_106) | ~m1_pre_topc(C_104, A_106) | ~l1_pre_topc(B_107) | ~v2_pre_topc(B_107) | v2_struct_0(B_107) | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106) | v2_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.28/1.26  tff(c_165, plain, (![A_106, D_105]: (k3_tmap_1(A_106, '#skF_2', '#skF_3', D_105, '#skF_4')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_105)) | ~m1_pre_topc(D_105, '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc(D_105, A_106) | ~m1_pre_topc('#skF_3', A_106) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106) | v2_struct_0(A_106))), inference(resolution, [status(thm)], [c_30, c_163])).
% 2.28/1.26  tff(c_168, plain, (![D_105, A_106]: (k7_relat_1('#skF_4', u1_struct_0(D_105))=k3_tmap_1(A_106, '#skF_2', '#skF_3', D_105, '#skF_4') | ~m1_pre_topc(D_105, '#skF_3') | ~m1_pre_topc(D_105, A_106) | ~m1_pre_topc('#skF_3', A_106) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106) | v2_struct_0(A_106))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_34, c_32, c_91, c_165])).
% 2.28/1.26  tff(c_170, plain, (![D_109, A_110]: (k7_relat_1('#skF_4', u1_struct_0(D_109))=k3_tmap_1(A_110, '#skF_2', '#skF_3', D_109, '#skF_4') | ~m1_pre_topc(D_109, '#skF_3') | ~m1_pre_topc(D_109, A_110) | ~m1_pre_topc('#skF_3', A_110) | ~l1_pre_topc(A_110) | ~v2_pre_topc(A_110) | v2_struct_0(A_110))), inference(negUnitSimplification, [status(thm)], [c_44, c_168])).
% 2.28/1.26  tff(c_174, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_170])).
% 2.28/1.26  tff(c_181, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_36, c_147, c_81, c_174])).
% 2.28/1.27  tff(c_182, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_50, c_181])).
% 2.28/1.27  tff(c_28, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.28/1.27  tff(c_183, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_182, c_28])).
% 2.28/1.27  tff(c_186, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_183])).
% 2.28/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.27  
% 2.28/1.27  Inference rules
% 2.28/1.27  ----------------------
% 2.28/1.27  #Ref     : 0
% 2.28/1.27  #Sup     : 24
% 2.28/1.27  #Fact    : 0
% 2.28/1.27  #Define  : 0
% 2.28/1.27  #Split   : 1
% 2.28/1.27  #Chain   : 0
% 2.28/1.27  #Close   : 0
% 2.28/1.27  
% 2.28/1.27  Ordering : KBO
% 2.28/1.27  
% 2.28/1.27  Simplification rules
% 2.28/1.27  ----------------------
% 2.28/1.27  #Subsume      : 1
% 2.28/1.27  #Demod        : 30
% 2.28/1.27  #Tautology    : 11
% 2.28/1.27  #SimpNegUnit  : 3
% 2.28/1.27  #BackRed      : 1
% 2.28/1.27  
% 2.28/1.27  #Partial instantiations: 0
% 2.28/1.27  #Strategies tried      : 1
% 2.28/1.27  
% 2.28/1.27  Timing (in seconds)
% 2.28/1.27  ----------------------
% 2.28/1.27  Preprocessing        : 0.34
% 2.28/1.27  Parsing              : 0.18
% 2.28/1.27  CNF conversion       : 0.03
% 2.28/1.27  Main loop            : 0.18
% 2.28/1.27  Inferencing          : 0.06
% 2.28/1.27  Reduction            : 0.06
% 2.28/1.27  Demodulation         : 0.04
% 2.28/1.27  BG Simplification    : 0.01
% 2.28/1.27  Subsumption          : 0.03
% 2.28/1.27  Abstraction          : 0.01
% 2.28/1.27  MUC search           : 0.00
% 2.28/1.27  Cooper               : 0.00
% 2.28/1.27  Total                : 0.55
% 2.28/1.27  Index Insertion      : 0.00
% 2.28/1.27  Index Deletion       : 0.00
% 2.28/1.27  Index Matching       : 0.00
% 2.28/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
