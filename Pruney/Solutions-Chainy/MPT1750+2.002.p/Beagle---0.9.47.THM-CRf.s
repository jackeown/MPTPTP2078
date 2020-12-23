%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:51 EST 2020

% Result     : Theorem 5.89s
% Output     : CNFRefutation 6.04s
% Verified   : 
% Statistics : Number of formulae       :  132 (2349 expanded)
%              Number of leaves         :   45 ( 836 expanded)
%              Depth                    :   25
%              Number of atoms          :  317 (10780 expanded)
%              Number of equality atoms :   28 ( 640 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(r1_funct_2,type,(
    r1_funct_2: ( $i * $i * $i * $i * $i * $i ) > $o )).

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

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_197,negated_conjecture,(
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
                  & m1_pre_topc(C,B) )
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,u1_struct_0(B),u1_struct_0(A))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
                   => ( g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                     => r1_funct_2(u1_struct_0(B),u1_struct_0(A),u1_struct_0(C),u1_struct_0(A),D,k2_tmap_1(B,A,D,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_tmap_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_150,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_164,axiom,(
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

tff(f_119,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(B)
        & ~ v1_xboole_0(D)
        & v1_funct_1(E)
        & v1_funct_2(E,A,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,C,D)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( r1_funct_2(A,B,C,D,E,F)
      <=> E = F ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

tff(f_81,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_146,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

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

tff(c_64,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_20,plain,(
    ! [A_18] :
      ( l1_struct_0(A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_54,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_58,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_38,plain,(
    ! [A_50] :
      ( m1_pre_topc(A_50,A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_74,plain,(
    ! [B_73,A_74] :
      ( l1_pre_topc(B_73)
      | ~ m1_pre_topc(B_73,A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_80,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_74])).

tff(c_84,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_80])).

tff(c_46,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_151,plain,(
    ! [A_93,B_94] :
      ( m1_pre_topc(A_93,g1_pre_topc(u1_struct_0(B_94),u1_pre_topc(B_94)))
      | ~ m1_pre_topc(A_93,B_94)
      | ~ l1_pre_topc(B_94)
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_167,plain,(
    ! [A_93] :
      ( m1_pre_topc(A_93,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_93,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_151])).

tff(c_212,plain,(
    ! [A_102] :
      ( m1_pre_topc(A_102,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_102,'#skF_2')
      | ~ l1_pre_topc(A_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_167])).

tff(c_26,plain,(
    ! [B_25,A_23] :
      ( m1_pre_topc(B_25,A_23)
      | ~ m1_pre_topc(B_25,g1_pre_topc(u1_struct_0(A_23),u1_pre_topc(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_218,plain,(
    ! [A_102] :
      ( m1_pre_topc(A_102,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_pre_topc(A_102,'#skF_2')
      | ~ l1_pre_topc(A_102) ) ),
    inference(resolution,[status(thm)],[c_212,c_26])).

tff(c_231,plain,(
    ! [A_103] :
      ( m1_pre_topc(A_103,'#skF_3')
      | ~ m1_pre_topc(A_103,'#skF_2')
      | ~ l1_pre_topc(A_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_218])).

tff(c_238,plain,
    ( m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_231])).

tff(c_245,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_238])).

tff(c_60,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_106,plain,(
    ! [B_83,A_84] :
      ( v2_pre_topc(B_83)
      | ~ m1_pre_topc(B_83,A_84)
      | ~ l1_pre_topc(A_84)
      | ~ v2_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_112,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_106])).

tff(c_116,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_112])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_329,plain,(
    ! [B_106,C_107,A_108] :
      ( m1_pre_topc(B_106,C_107)
      | ~ r1_tarski(u1_struct_0(B_106),u1_struct_0(C_107))
      | ~ m1_pre_topc(C_107,A_108)
      | ~ m1_pre_topc(B_106,A_108)
      | ~ l1_pre_topc(A_108)
      | ~ v2_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_334,plain,(
    ! [B_109,A_110] :
      ( m1_pre_topc(B_109,B_109)
      | ~ m1_pre_topc(B_109,A_110)
      | ~ l1_pre_topc(A_110)
      | ~ v2_pre_topc(A_110) ) ),
    inference(resolution,[status(thm)],[c_6,c_329])).

tff(c_340,plain,
    ( m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_245,c_334])).

tff(c_357,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_84,c_340])).

tff(c_390,plain,(
    ! [B_111,C_112,A_113] :
      ( r1_tarski(u1_struct_0(B_111),u1_struct_0(C_112))
      | ~ m1_pre_topc(B_111,C_112)
      | ~ m1_pre_topc(C_112,A_113)
      | ~ m1_pre_topc(B_111,A_113)
      | ~ l1_pre_topc(A_113)
      | ~ v2_pre_topc(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_392,plain,(
    ! [B_111] :
      ( r1_tarski(u1_struct_0(B_111),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_111,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_357,c_390])).

tff(c_411,plain,(
    ! [B_111] :
      ( r1_tarski(u1_struct_0(B_111),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_111,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_392])).

tff(c_241,plain,
    ( m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_231])).

tff(c_248,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_241])).

tff(c_396,plain,(
    ! [B_111] :
      ( r1_tarski(u1_struct_0(B_111),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_111,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_248,c_390])).

tff(c_435,plain,(
    ! [B_115] :
      ( r1_tarski(u1_struct_0(B_115),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_115,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_84,c_396])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_456,plain,(
    ! [B_119] :
      ( u1_struct_0(B_119) = u1_struct_0('#skF_3')
      | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0(B_119))
      | ~ m1_pre_topc(B_119,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_435,c_2])).

tff(c_464,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_411,c_456])).

tff(c_476,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_245,c_464])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_50,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_485,plain,(
    ! [A_122,B_121,F_123,D_120,C_124] :
      ( r1_funct_2(A_122,B_121,C_124,D_120,F_123,F_123)
      | ~ m1_subset_1(F_123,k1_zfmisc_1(k2_zfmisc_1(C_124,D_120)))
      | ~ v1_funct_2(F_123,C_124,D_120)
      | ~ m1_subset_1(F_123,k1_zfmisc_1(k2_zfmisc_1(A_122,B_121)))
      | ~ v1_funct_2(F_123,A_122,B_121)
      | ~ v1_funct_1(F_123)
      | v1_xboole_0(D_120)
      | v1_xboole_0(B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_487,plain,(
    ! [A_122,B_121] :
      ( r1_funct_2(A_122,B_121,u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_122,B_121)))
      | ~ v1_funct_2('#skF_4',A_122,B_121)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_121) ) ),
    inference(resolution,[status(thm)],[c_48,c_485])).

tff(c_490,plain,(
    ! [A_122,B_121] :
      ( r1_funct_2(A_122,B_121,u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_122,B_121)))
      | ~ v1_funct_2('#skF_4',A_122,B_121)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_487])).

tff(c_958,plain,(
    ! [A_122,B_121] :
      ( r1_funct_2(A_122,B_121,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_122,B_121)))
      | ~ v1_funct_2('#skF_4',A_122,B_121)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_476,c_490])).

tff(c_959,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_958])).

tff(c_24,plain,(
    ! [A_22] :
      ( ~ v1_xboole_0(u1_struct_0(A_22))
      | ~ l1_struct_0(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_962,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_959,c_24])).

tff(c_965,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_962])).

tff(c_968,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_965])).

tff(c_972,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_968])).

tff(c_974,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_958])).

tff(c_498,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_476,c_50])).

tff(c_497,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_476,c_48])).

tff(c_32,plain,(
    ! [A_29,F_34,D_32,C_31,B_30] :
      ( r1_funct_2(A_29,B_30,C_31,D_32,F_34,F_34)
      | ~ m1_subset_1(F_34,k1_zfmisc_1(k2_zfmisc_1(C_31,D_32)))
      | ~ v1_funct_2(F_34,C_31,D_32)
      | ~ m1_subset_1(F_34,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30)))
      | ~ v1_funct_2(F_34,A_29,B_30)
      | ~ v1_funct_1(F_34)
      | v1_xboole_0(D_32)
      | v1_xboole_0(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_572,plain,(
    ! [A_29,B_30] :
      ( r1_funct_2(A_29,B_30,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_29,B_30)))
      | ~ v1_funct_2('#skF_4',A_29,B_30)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_30) ) ),
    inference(resolution,[status(thm)],[c_497,c_32])).

tff(c_586,plain,(
    ! [A_29,B_30] :
      ( r1_funct_2(A_29,B_30,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_29,B_30)))
      | ~ v1_funct_2('#skF_4',A_29,B_30)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_498,c_572])).

tff(c_1790,plain,(
    ! [A_194,B_195] :
      ( r1_funct_2(A_194,B_195,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_194,B_195)))
      | ~ v1_funct_2('#skF_4',A_194,B_195)
      | v1_xboole_0(B_195) ) ),
    inference(negUnitSimplification,[status(thm)],[c_974,c_586])).

tff(c_66,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_176,plain,(
    ! [A_95,B_96,C_97,D_98] :
      ( k2_partfun1(A_95,B_96,C_97,D_98) = k7_relat_1(C_97,D_98)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96)))
      | ~ v1_funct_1(C_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_178,plain,(
    ! [D_98] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_98) = k7_relat_1('#skF_4',D_98)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_176])).

tff(c_181,plain,(
    ! [D_98] : k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_98) = k7_relat_1('#skF_4',D_98) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_178])).

tff(c_492,plain,(
    ! [D_98] : k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',D_98) = k7_relat_1('#skF_4',D_98) ),
    inference(demodulation,[status(thm),theory(equality)],[c_476,c_181])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_687,plain,(
    ! [A_135,B_136,C_137,D_138] :
      ( k2_partfun1(u1_struct_0(A_135),u1_struct_0(B_136),C_137,u1_struct_0(D_138)) = k2_tmap_1(A_135,B_136,C_137,D_138)
      | ~ m1_pre_topc(D_138,A_135)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_135),u1_struct_0(B_136))))
      | ~ v1_funct_2(C_137,u1_struct_0(A_135),u1_struct_0(B_136))
      | ~ v1_funct_1(C_137)
      | ~ l1_pre_topc(B_136)
      | ~ v2_pre_topc(B_136)
      | v2_struct_0(B_136)
      | ~ l1_pre_topc(A_135)
      | ~ v2_pre_topc(A_135)
      | v2_struct_0(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_691,plain,(
    ! [B_136,C_137,D_138] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0(B_136),C_137,u1_struct_0(D_138)) = k2_tmap_1('#skF_2',B_136,C_137,D_138)
      | ~ m1_pre_topc(D_138,'#skF_2')
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_136))))
      | ~ v1_funct_2(C_137,u1_struct_0('#skF_2'),u1_struct_0(B_136))
      | ~ v1_funct_1(C_137)
      | ~ l1_pre_topc(B_136)
      | ~ v2_pre_topc(B_136)
      | v2_struct_0(B_136)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_476,c_687])).

tff(c_699,plain,(
    ! [B_136,C_137,D_138] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_136),C_137,u1_struct_0(D_138)) = k2_tmap_1('#skF_2',B_136,C_137,D_138)
      | ~ m1_pre_topc(D_138,'#skF_2')
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_136))))
      | ~ v1_funct_2(C_137,u1_struct_0('#skF_3'),u1_struct_0(B_136))
      | ~ v1_funct_1(C_137)
      | ~ l1_pre_topc(B_136)
      | ~ v2_pre_topc(B_136)
      | v2_struct_0(B_136)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_476,c_476,c_691])).

tff(c_975,plain,(
    ! [B_151,C_152,D_153] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_151),C_152,u1_struct_0(D_153)) = k2_tmap_1('#skF_2',B_151,C_152,D_153)
      | ~ m1_pre_topc(D_153,'#skF_2')
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_151))))
      | ~ v1_funct_2(C_152,u1_struct_0('#skF_3'),u1_struct_0(B_151))
      | ~ v1_funct_1(C_152)
      | ~ l1_pre_topc(B_151)
      | ~ v2_pre_topc(B_151)
      | v2_struct_0(B_151) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_699])).

tff(c_977,plain,(
    ! [D_153] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_153)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_153)
      | ~ m1_pre_topc(D_153,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_497,c_975])).

tff(c_982,plain,(
    ! [D_153] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_153)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_153)
      | ~ m1_pre_topc(D_153,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_52,c_498,c_492,c_977])).

tff(c_987,plain,(
    ! [D_154] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_154)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_154)
      | ~ m1_pre_topc(D_154,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_982])).

tff(c_10,plain,(
    ! [C_7,A_5,B_6] :
      ( v1_relat_1(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_96,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_10])).

tff(c_101,plain,(
    ! [C_80,A_81,B_82] :
      ( v4_relat_1(C_80,A_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_105,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_101])).

tff(c_122,plain,(
    ! [B_88,A_89] :
      ( k7_relat_1(B_88,A_89) = B_88
      | ~ v4_relat_1(B_88,A_89)
      | ~ v1_relat_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_125,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_105,c_122])).

tff(c_128,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_125])).

tff(c_494,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_476,c_128])).

tff(c_996,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_987,c_494])).

tff(c_1011,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_996])).

tff(c_44,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_493,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_476,c_44])).

tff(c_1017,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1011,c_493])).

tff(c_1793,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1790,c_1017])).

tff(c_1798,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_497,c_1793])).

tff(c_1800,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_974,c_1798])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:34:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.89/2.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.04/2.46  
% 6.04/2.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.04/2.46  %$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.04/2.46  
% 6.04/2.46  %Foreground sorts:
% 6.04/2.46  
% 6.04/2.46  
% 6.04/2.46  %Background operators:
% 6.04/2.46  
% 6.04/2.46  
% 6.04/2.46  %Foreground operators:
% 6.04/2.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.04/2.46  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 6.04/2.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.04/2.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.04/2.46  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 6.04/2.46  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.04/2.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.04/2.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.04/2.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.04/2.46  tff('#skF_2', type, '#skF_2': $i).
% 6.04/2.46  tff('#skF_3', type, '#skF_3': $i).
% 6.04/2.46  tff('#skF_1', type, '#skF_1': $i).
% 6.04/2.46  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.04/2.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.04/2.46  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.04/2.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.04/2.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.04/2.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.04/2.46  tff('#skF_4', type, '#skF_4': $i).
% 6.04/2.46  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 6.04/2.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.04/2.46  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.04/2.46  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 6.04/2.46  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.04/2.46  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.04/2.46  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 6.04/2.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.04/2.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.04/2.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.04/2.46  
% 6.04/2.50  tff(f_197, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_tmap_1)).
% 6.04/2.50  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.04/2.50  tff(f_150, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 6.04/2.50  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 6.04/2.50  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 6.04/2.50  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 6.04/2.50  tff(f_62, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 6.04/2.50  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.04/2.50  tff(f_164, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 6.04/2.50  tff(f_119, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 6.04/2.50  tff(f_81, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 6.04/2.50  tff(f_53, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 6.04/2.50  tff(f_146, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 6.04/2.50  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.04/2.50  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.04/2.50  tff(f_37, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 6.04/2.50  tff(c_64, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_197])).
% 6.04/2.50  tff(c_20, plain, (![A_18]: (l1_struct_0(A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.04/2.50  tff(c_68, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_197])).
% 6.04/2.50  tff(c_54, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 6.04/2.50  tff(c_58, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 6.04/2.50  tff(c_38, plain, (![A_50]: (m1_pre_topc(A_50, A_50) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_150])).
% 6.04/2.50  tff(c_74, plain, (![B_73, A_74]: (l1_pre_topc(B_73) | ~m1_pre_topc(B_73, A_74) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.04/2.50  tff(c_80, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_74])).
% 6.04/2.50  tff(c_84, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_80])).
% 6.04/2.50  tff(c_46, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_197])).
% 6.04/2.50  tff(c_151, plain, (![A_93, B_94]: (m1_pre_topc(A_93, g1_pre_topc(u1_struct_0(B_94), u1_pre_topc(B_94))) | ~m1_pre_topc(A_93, B_94) | ~l1_pre_topc(B_94) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.04/2.50  tff(c_167, plain, (![A_93]: (m1_pre_topc(A_93, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_93, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_93))), inference(superposition, [status(thm), theory('equality')], [c_46, c_151])).
% 6.04/2.50  tff(c_212, plain, (![A_102]: (m1_pre_topc(A_102, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_102, '#skF_2') | ~l1_pre_topc(A_102))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_167])).
% 6.04/2.50  tff(c_26, plain, (![B_25, A_23]: (m1_pre_topc(B_25, A_23) | ~m1_pre_topc(B_25, g1_pre_topc(u1_struct_0(A_23), u1_pre_topc(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.04/2.50  tff(c_218, plain, (![A_102]: (m1_pre_topc(A_102, '#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc(A_102, '#skF_2') | ~l1_pre_topc(A_102))), inference(resolution, [status(thm)], [c_212, c_26])).
% 6.04/2.50  tff(c_231, plain, (![A_103]: (m1_pre_topc(A_103, '#skF_3') | ~m1_pre_topc(A_103, '#skF_2') | ~l1_pre_topc(A_103))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_218])).
% 6.04/2.50  tff(c_238, plain, (m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_231])).
% 6.04/2.50  tff(c_245, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_238])).
% 6.04/2.50  tff(c_60, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 6.04/2.50  tff(c_106, plain, (![B_83, A_84]: (v2_pre_topc(B_83) | ~m1_pre_topc(B_83, A_84) | ~l1_pre_topc(A_84) | ~v2_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.04/2.50  tff(c_112, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_106])).
% 6.04/2.50  tff(c_116, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_112])).
% 6.04/2.50  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.04/2.50  tff(c_329, plain, (![B_106, C_107, A_108]: (m1_pre_topc(B_106, C_107) | ~r1_tarski(u1_struct_0(B_106), u1_struct_0(C_107)) | ~m1_pre_topc(C_107, A_108) | ~m1_pre_topc(B_106, A_108) | ~l1_pre_topc(A_108) | ~v2_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_164])).
% 6.04/2.50  tff(c_334, plain, (![B_109, A_110]: (m1_pre_topc(B_109, B_109) | ~m1_pre_topc(B_109, A_110) | ~l1_pre_topc(A_110) | ~v2_pre_topc(A_110))), inference(resolution, [status(thm)], [c_6, c_329])).
% 6.04/2.50  tff(c_340, plain, (m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_245, c_334])).
% 6.04/2.50  tff(c_357, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_84, c_340])).
% 6.04/2.50  tff(c_390, plain, (![B_111, C_112, A_113]: (r1_tarski(u1_struct_0(B_111), u1_struct_0(C_112)) | ~m1_pre_topc(B_111, C_112) | ~m1_pre_topc(C_112, A_113) | ~m1_pre_topc(B_111, A_113) | ~l1_pre_topc(A_113) | ~v2_pre_topc(A_113))), inference(cnfTransformation, [status(thm)], [f_164])).
% 6.04/2.50  tff(c_392, plain, (![B_111]: (r1_tarski(u1_struct_0(B_111), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_111, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_357, c_390])).
% 6.04/2.50  tff(c_411, plain, (![B_111]: (r1_tarski(u1_struct_0(B_111), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_111, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_392])).
% 6.04/2.50  tff(c_241, plain, (m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_54, c_231])).
% 6.04/2.50  tff(c_248, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_241])).
% 6.04/2.50  tff(c_396, plain, (![B_111]: (r1_tarski(u1_struct_0(B_111), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_111, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_248, c_390])).
% 6.04/2.50  tff(c_435, plain, (![B_115]: (r1_tarski(u1_struct_0(B_115), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_115, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_84, c_396])).
% 6.04/2.50  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.04/2.50  tff(c_456, plain, (![B_119]: (u1_struct_0(B_119)=u1_struct_0('#skF_3') | ~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0(B_119)) | ~m1_pre_topc(B_119, '#skF_3'))), inference(resolution, [status(thm)], [c_435, c_2])).
% 6.04/2.50  tff(c_464, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_411, c_456])).
% 6.04/2.50  tff(c_476, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_245, c_464])).
% 6.04/2.50  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_197])).
% 6.04/2.50  tff(c_50, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_197])).
% 6.04/2.50  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_197])).
% 6.04/2.50  tff(c_485, plain, (![A_122, B_121, F_123, D_120, C_124]: (r1_funct_2(A_122, B_121, C_124, D_120, F_123, F_123) | ~m1_subset_1(F_123, k1_zfmisc_1(k2_zfmisc_1(C_124, D_120))) | ~v1_funct_2(F_123, C_124, D_120) | ~m1_subset_1(F_123, k1_zfmisc_1(k2_zfmisc_1(A_122, B_121))) | ~v1_funct_2(F_123, A_122, B_121) | ~v1_funct_1(F_123) | v1_xboole_0(D_120) | v1_xboole_0(B_121))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.04/2.50  tff(c_487, plain, (![A_122, B_121]: (r1_funct_2(A_122, B_121, u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_122, B_121))) | ~v1_funct_2('#skF_4', A_122, B_121) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_121))), inference(resolution, [status(thm)], [c_48, c_485])).
% 6.04/2.50  tff(c_490, plain, (![A_122, B_121]: (r1_funct_2(A_122, B_121, u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_122, B_121))) | ~v1_funct_2('#skF_4', A_122, B_121) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_121))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_487])).
% 6.04/2.50  tff(c_958, plain, (![A_122, B_121]: (r1_funct_2(A_122, B_121, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_122, B_121))) | ~v1_funct_2('#skF_4', A_122, B_121) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_121))), inference(demodulation, [status(thm), theory('equality')], [c_476, c_490])).
% 6.04/2.50  tff(c_959, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_958])).
% 6.04/2.50  tff(c_24, plain, (![A_22]: (~v1_xboole_0(u1_struct_0(A_22)) | ~l1_struct_0(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.04/2.50  tff(c_962, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_959, c_24])).
% 6.04/2.50  tff(c_965, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_68, c_962])).
% 6.04/2.50  tff(c_968, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_965])).
% 6.04/2.50  tff(c_972, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_968])).
% 6.04/2.50  tff(c_974, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_958])).
% 6.04/2.50  tff(c_498, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_476, c_50])).
% 6.04/2.50  tff(c_497, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_476, c_48])).
% 6.04/2.50  tff(c_32, plain, (![A_29, F_34, D_32, C_31, B_30]: (r1_funct_2(A_29, B_30, C_31, D_32, F_34, F_34) | ~m1_subset_1(F_34, k1_zfmisc_1(k2_zfmisc_1(C_31, D_32))) | ~v1_funct_2(F_34, C_31, D_32) | ~m1_subset_1(F_34, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))) | ~v1_funct_2(F_34, A_29, B_30) | ~v1_funct_1(F_34) | v1_xboole_0(D_32) | v1_xboole_0(B_30))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.04/2.50  tff(c_572, plain, (![A_29, B_30]: (r1_funct_2(A_29, B_30, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))) | ~v1_funct_2('#skF_4', A_29, B_30) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_30))), inference(resolution, [status(thm)], [c_497, c_32])).
% 6.04/2.50  tff(c_586, plain, (![A_29, B_30]: (r1_funct_2(A_29, B_30, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))) | ~v1_funct_2('#skF_4', A_29, B_30) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_30))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_498, c_572])).
% 6.04/2.50  tff(c_1790, plain, (![A_194, B_195]: (r1_funct_2(A_194, B_195, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_194, B_195))) | ~v1_funct_2('#skF_4', A_194, B_195) | v1_xboole_0(B_195))), inference(negUnitSimplification, [status(thm)], [c_974, c_586])).
% 6.04/2.50  tff(c_66, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_197])).
% 6.04/2.50  tff(c_176, plain, (![A_95, B_96, C_97, D_98]: (k2_partfun1(A_95, B_96, C_97, D_98)=k7_relat_1(C_97, D_98) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))) | ~v1_funct_1(C_97))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.04/2.50  tff(c_178, plain, (![D_98]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_98)=k7_relat_1('#skF_4', D_98) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_176])).
% 6.04/2.50  tff(c_181, plain, (![D_98]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_98)=k7_relat_1('#skF_4', D_98))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_178])).
% 6.04/2.50  tff(c_492, plain, (![D_98]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', D_98)=k7_relat_1('#skF_4', D_98))), inference(demodulation, [status(thm), theory('equality')], [c_476, c_181])).
% 6.04/2.50  tff(c_62, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 6.04/2.50  tff(c_687, plain, (![A_135, B_136, C_137, D_138]: (k2_partfun1(u1_struct_0(A_135), u1_struct_0(B_136), C_137, u1_struct_0(D_138))=k2_tmap_1(A_135, B_136, C_137, D_138) | ~m1_pre_topc(D_138, A_135) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_135), u1_struct_0(B_136)))) | ~v1_funct_2(C_137, u1_struct_0(A_135), u1_struct_0(B_136)) | ~v1_funct_1(C_137) | ~l1_pre_topc(B_136) | ~v2_pre_topc(B_136) | v2_struct_0(B_136) | ~l1_pre_topc(A_135) | ~v2_pre_topc(A_135) | v2_struct_0(A_135))), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.04/2.50  tff(c_691, plain, (![B_136, C_137, D_138]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_136), C_137, u1_struct_0(D_138))=k2_tmap_1('#skF_2', B_136, C_137, D_138) | ~m1_pre_topc(D_138, '#skF_2') | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_136)))) | ~v1_funct_2(C_137, u1_struct_0('#skF_2'), u1_struct_0(B_136)) | ~v1_funct_1(C_137) | ~l1_pre_topc(B_136) | ~v2_pre_topc(B_136) | v2_struct_0(B_136) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_476, c_687])).
% 6.04/2.50  tff(c_699, plain, (![B_136, C_137, D_138]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_136), C_137, u1_struct_0(D_138))=k2_tmap_1('#skF_2', B_136, C_137, D_138) | ~m1_pre_topc(D_138, '#skF_2') | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_136)))) | ~v1_funct_2(C_137, u1_struct_0('#skF_3'), u1_struct_0(B_136)) | ~v1_funct_1(C_137) | ~l1_pre_topc(B_136) | ~v2_pre_topc(B_136) | v2_struct_0(B_136) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_476, c_476, c_691])).
% 6.04/2.50  tff(c_975, plain, (![B_151, C_152, D_153]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_151), C_152, u1_struct_0(D_153))=k2_tmap_1('#skF_2', B_151, C_152, D_153) | ~m1_pre_topc(D_153, '#skF_2') | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_151)))) | ~v1_funct_2(C_152, u1_struct_0('#skF_3'), u1_struct_0(B_151)) | ~v1_funct_1(C_152) | ~l1_pre_topc(B_151) | ~v2_pre_topc(B_151) | v2_struct_0(B_151))), inference(negUnitSimplification, [status(thm)], [c_62, c_699])).
% 6.04/2.50  tff(c_977, plain, (![D_153]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_153))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_153) | ~m1_pre_topc(D_153, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_497, c_975])).
% 6.04/2.50  tff(c_982, plain, (![D_153]: (k7_relat_1('#skF_4', u1_struct_0(D_153))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_153) | ~m1_pre_topc(D_153, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_52, c_498, c_492, c_977])).
% 6.04/2.50  tff(c_987, plain, (![D_154]: (k7_relat_1('#skF_4', u1_struct_0(D_154))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_154) | ~m1_pre_topc(D_154, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_68, c_982])).
% 6.04/2.50  tff(c_10, plain, (![C_7, A_5, B_6]: (v1_relat_1(C_7) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.04/2.50  tff(c_96, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_10])).
% 6.04/2.50  tff(c_101, plain, (![C_80, A_81, B_82]: (v4_relat_1(C_80, A_81) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.04/2.50  tff(c_105, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_101])).
% 6.04/2.50  tff(c_122, plain, (![B_88, A_89]: (k7_relat_1(B_88, A_89)=B_88 | ~v4_relat_1(B_88, A_89) | ~v1_relat_1(B_88))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.04/2.50  tff(c_125, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_105, c_122])).
% 6.04/2.50  tff(c_128, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_125])).
% 6.04/2.50  tff(c_494, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_476, c_128])).
% 6.04/2.50  tff(c_996, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_987, c_494])).
% 6.04/2.50  tff(c_1011, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_996])).
% 6.04/2.50  tff(c_44, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_197])).
% 6.04/2.50  tff(c_493, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_476, c_44])).
% 6.04/2.50  tff(c_1017, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1011, c_493])).
% 6.04/2.50  tff(c_1793, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_1790, c_1017])).
% 6.04/2.50  tff(c_1798, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_498, c_497, c_1793])).
% 6.04/2.50  tff(c_1800, plain, $false, inference(negUnitSimplification, [status(thm)], [c_974, c_1798])).
% 6.04/2.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.04/2.50  
% 6.04/2.50  Inference rules
% 6.04/2.50  ----------------------
% 6.04/2.50  #Ref     : 0
% 6.04/2.50  #Sup     : 333
% 6.04/2.50  #Fact    : 0
% 6.04/2.50  #Define  : 0
% 6.04/2.50  #Split   : 3
% 6.04/2.50  #Chain   : 0
% 6.04/2.50  #Close   : 0
% 6.04/2.50  
% 6.04/2.50  Ordering : KBO
% 6.04/2.50  
% 6.04/2.50  Simplification rules
% 6.04/2.50  ----------------------
% 6.04/2.50  #Subsume      : 93
% 6.04/2.50  #Demod        : 516
% 6.04/2.50  #Tautology    : 152
% 6.04/2.50  #SimpNegUnit  : 11
% 6.04/2.50  #BackRed      : 9
% 6.04/2.50  
% 6.04/2.50  #Partial instantiations: 0
% 6.04/2.50  #Strategies tried      : 1
% 6.04/2.50  
% 6.04/2.50  Timing (in seconds)
% 6.04/2.50  ----------------------
% 6.04/2.50  Preprocessing        : 0.57
% 6.04/2.50  Parsing              : 0.29
% 6.04/2.50  CNF conversion       : 0.05
% 6.04/2.50  Main loop            : 0.95
% 6.04/2.50  Inferencing          : 0.32
% 6.04/2.50  Reduction            : 0.32
% 6.04/2.51  Demodulation         : 0.23
% 6.04/2.51  BG Simplification    : 0.04
% 6.04/2.51  Subsumption          : 0.21
% 6.04/2.51  Abstraction          : 0.04
% 6.04/2.51  MUC search           : 0.00
% 6.04/2.51  Cooper               : 0.00
% 6.04/2.51  Total                : 1.60
% 6.04/2.51  Index Insertion      : 0.00
% 6.04/2.51  Index Deletion       : 0.00
% 6.04/2.51  Index Matching       : 0.00
% 6.04/2.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
