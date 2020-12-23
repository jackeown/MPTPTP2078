%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:52 EST 2020

% Result     : Theorem 6.02s
% Output     : CNFRefutation 6.02s
% Verified   : 
% Statistics : Number of formulae       :  126 (4299 expanded)
%              Number of leaves         :   41 (1507 expanded)
%              Depth                    :   28
%              Number of atoms          :  322 (19863 expanded)
%              Number of equality atoms :   31 (1157 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

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

tff(r1_funct_2,type,(
    r1_funct_2: ( $i * $i * $i * $i * $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_199,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_tmap_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_152,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_166,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_121,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(B)
        & ~ v1_xboole_0(D)
        & v1_funct_1(E)
        & v1_funct_2(E,A,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,C,D)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => r1_funct_2(A,B,C,D,E,E) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).

tff(f_85,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_148,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(A,C)
       => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_39,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(c_62,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_20,plain,(
    ! [A_18] :
      ( l1_struct_0(A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_56,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_52,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_72,plain,(
    ! [B_73,A_74] :
      ( l1_pre_topc(B_73)
      | ~ m1_pre_topc(B_73,A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_78,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_72])).

tff(c_82,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_78])).

tff(c_44,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_134,plain,(
    ! [A_90,B_91] :
      ( m1_pre_topc(A_90,g1_pre_topc(u1_struct_0(B_91),u1_pre_topc(B_91)))
      | ~ m1_pre_topc(A_90,B_91)
      | ~ l1_pre_topc(B_91)
      | ~ l1_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_150,plain,(
    ! [A_90] :
      ( m1_pre_topc(A_90,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_90,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_134])).

tff(c_180,plain,(
    ! [A_94] :
      ( m1_pre_topc(A_94,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_94,'#skF_2')
      | ~ l1_pre_topc(A_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_150])).

tff(c_26,plain,(
    ! [B_25,A_23] :
      ( m1_pre_topc(B_25,A_23)
      | ~ m1_pre_topc(B_25,g1_pre_topc(u1_struct_0(A_23),u1_pre_topc(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_186,plain,(
    ! [A_94] :
      ( m1_pre_topc(A_94,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_pre_topc(A_94,'#skF_2')
      | ~ l1_pre_topc(A_94) ) ),
    inference(resolution,[status(thm)],[c_180,c_26])).

tff(c_199,plain,(
    ! [A_95] :
      ( m1_pre_topc(A_95,'#skF_3')
      | ~ m1_pre_topc(A_95,'#skF_2')
      | ~ l1_pre_topc(A_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_186])).

tff(c_209,plain,
    ( m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_199])).

tff(c_216,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_209])).

tff(c_36,plain,(
    ! [A_50] :
      ( m1_pre_topc(A_50,A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_206,plain,
    ( m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_199])).

tff(c_213,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_206])).

tff(c_58,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_90,plain,(
    ! [B_77,A_78] :
      ( v2_pre_topc(B_77)
      | ~ m1_pre_topc(B_77,A_78)
      | ~ l1_pre_topc(A_78)
      | ~ v2_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_96,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_90])).

tff(c_100,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_96])).

tff(c_38,plain,(
    ! [B_55,C_57,A_51] :
      ( r1_tarski(u1_struct_0(B_55),u1_struct_0(C_57))
      | ~ m1_pre_topc(B_55,C_57)
      | ~ m1_pre_topc(C_57,A_51)
      | ~ m1_pre_topc(B_55,A_51)
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_238,plain,(
    ! [B_55] :
      ( r1_tarski(u1_struct_0(B_55),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_55,'#skF_2')
      | ~ m1_pre_topc(B_55,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_213,c_38])).

tff(c_250,plain,(
    ! [B_55] :
      ( r1_tarski(u1_struct_0(B_55),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_55,'#skF_2')
      | ~ m1_pre_topc(B_55,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_82,c_238])).

tff(c_261,plain,(
    ! [B_55] :
      ( r1_tarski(u1_struct_0(B_55),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_55,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_216,c_38])).

tff(c_283,plain,(
    ! [B_99] :
      ( r1_tarski(u1_struct_0(B_99),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_99,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_82,c_261])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_295,plain,(
    ! [B_103] :
      ( u1_struct_0(B_103) = u1_struct_0('#skF_3')
      | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0(B_103))
      | ~ m1_pre_topc(B_103,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_283,c_2])).

tff(c_303,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_250,c_295])).

tff(c_315,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_52,c_213,c_303])).

tff(c_48,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_330,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_48])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_329,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_46])).

tff(c_1247,plain,(
    ! [E_162,B_159,C_163,D_158,A_160,F_161] :
      ( r1_funct_2(A_160,B_159,C_163,D_158,E_162,E_162)
      | ~ m1_subset_1(F_161,k1_zfmisc_1(k2_zfmisc_1(C_163,D_158)))
      | ~ v1_funct_2(F_161,C_163,D_158)
      | ~ v1_funct_1(F_161)
      | ~ m1_subset_1(E_162,k1_zfmisc_1(k2_zfmisc_1(A_160,B_159)))
      | ~ v1_funct_2(E_162,A_160,B_159)
      | ~ v1_funct_1(E_162)
      | v1_xboole_0(D_158)
      | v1_xboole_0(B_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1251,plain,(
    ! [A_160,B_159,E_162] :
      ( r1_funct_2(A_160,B_159,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),E_162,E_162)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_162,k1_zfmisc_1(k2_zfmisc_1(A_160,B_159)))
      | ~ v1_funct_2(E_162,A_160,B_159)
      | ~ v1_funct_1(E_162)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_159) ) ),
    inference(resolution,[status(thm)],[c_329,c_1247])).

tff(c_1255,plain,(
    ! [A_160,B_159,E_162] :
      ( r1_funct_2(A_160,B_159,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),E_162,E_162)
      | ~ m1_subset_1(E_162,k1_zfmisc_1(k2_zfmisc_1(A_160,B_159)))
      | ~ v1_funct_2(E_162,A_160,B_159)
      | ~ v1_funct_1(E_162)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_159) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_330,c_1251])).

tff(c_1328,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1255])).

tff(c_24,plain,(
    ! [A_22] :
      ( ~ v1_xboole_0(u1_struct_0(A_22))
      | ~ l1_struct_0(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1331,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1328,c_24])).

tff(c_1334,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1331])).

tff(c_1337,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_1334])).

tff(c_1341,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1337])).

tff(c_1343,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1255])).

tff(c_4166,plain,(
    ! [A_331,B_332,E_333] :
      ( r1_funct_2(A_331,B_332,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),E_333,E_333)
      | ~ m1_subset_1(E_333,k1_zfmisc_1(k2_zfmisc_1(A_331,B_332)))
      | ~ v1_funct_2(E_333,A_331,B_332)
      | ~ v1_funct_1(E_333)
      | v1_xboole_0(B_332) ) ),
    inference(splitRight,[status(thm)],[c_1255])).

tff(c_64,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_1433,plain,(
    ! [A_170,B_171,C_172,D_173] :
      ( k2_partfun1(u1_struct_0(A_170),u1_struct_0(B_171),C_172,u1_struct_0(D_173)) = k2_tmap_1(A_170,B_171,C_172,D_173)
      | ~ m1_pre_topc(D_173,A_170)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_170),u1_struct_0(B_171))))
      | ~ v1_funct_2(C_172,u1_struct_0(A_170),u1_struct_0(B_171))
      | ~ v1_funct_1(C_172)
      | ~ l1_pre_topc(B_171)
      | ~ v2_pre_topc(B_171)
      | v2_struct_0(B_171)
      | ~ l1_pre_topc(A_170)
      | ~ v2_pre_topc(A_170)
      | v2_struct_0(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_1440,plain,(
    ! [B_171,C_172,D_173] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0(B_171),C_172,u1_struct_0(D_173)) = k2_tmap_1('#skF_2',B_171,C_172,D_173)
      | ~ m1_pre_topc(D_173,'#skF_2')
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_171))))
      | ~ v1_funct_2(C_172,u1_struct_0('#skF_2'),u1_struct_0(B_171))
      | ~ v1_funct_1(C_172)
      | ~ l1_pre_topc(B_171)
      | ~ v2_pre_topc(B_171)
      | v2_struct_0(B_171)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_1433])).

tff(c_1449,plain,(
    ! [B_171,C_172,D_173] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_171),C_172,u1_struct_0(D_173)) = k2_tmap_1('#skF_2',B_171,C_172,D_173)
      | ~ m1_pre_topc(D_173,'#skF_2')
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_171))))
      | ~ v1_funct_2(C_172,u1_struct_0('#skF_3'),u1_struct_0(B_171))
      | ~ v1_funct_1(C_172)
      | ~ l1_pre_topc(B_171)
      | ~ v2_pre_topc(B_171)
      | v2_struct_0(B_171)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_315,c_315,c_1440])).

tff(c_1908,plain,(
    ! [B_202,C_203,D_204] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_202),C_203,u1_struct_0(D_204)) = k2_tmap_1('#skF_2',B_202,C_203,D_204)
      | ~ m1_pre_topc(D_204,'#skF_2')
      | ~ m1_subset_1(C_203,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_202))))
      | ~ v1_funct_2(C_203,u1_struct_0('#skF_3'),u1_struct_0(B_202))
      | ~ v1_funct_1(C_203)
      | ~ l1_pre_topc(B_202)
      | ~ v2_pre_topc(B_202)
      | v2_struct_0(B_202) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1449])).

tff(c_1915,plain,(
    ! [D_204] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_204)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_204)
      | ~ m1_pre_topc(D_204,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_329,c_1908])).

tff(c_1925,plain,(
    ! [D_204] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_204)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_204)
      | ~ m1_pre_topc(D_204,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_50,c_330,c_1915])).

tff(c_1936,plain,(
    ! [D_205] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_205)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_205)
      | ~ m1_pre_topc(D_205,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1925])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_1438,plain,(
    ! [D_173] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_173)) = k2_tmap_1('#skF_3','#skF_1','#skF_4',D_173)
      | ~ m1_pre_topc(D_173,'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_329,c_1433])).

tff(c_1446,plain,(
    ! [D_173] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_173)) = k2_tmap_1('#skF_3','#skF_1','#skF_4',D_173)
      | ~ m1_pre_topc(D_173,'#skF_3')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_82,c_64,c_62,c_50,c_330,c_1438])).

tff(c_1536,plain,(
    ! [D_176] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_176)) = k2_tmap_1('#skF_3','#skF_1','#skF_4',D_176)
      | ~ m1_pre_topc(D_176,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_66,c_1446])).

tff(c_1559,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0('#skF_3')) = k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_1536])).

tff(c_1565,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0('#skF_3')) = k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_1559])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9,D_10] :
      ( m1_subset_1(k2_partfun1(A_7,B_8,C_9,D_10),k1_zfmisc_1(k2_zfmisc_1(A_7,B_8)))
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8)))
      | ~ v1_funct_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1038,plain,(
    ! [A_144,B_145,D_146,C_147] :
      ( r2_relset_1(A_144,B_145,k2_partfun1(A_144,B_145,D_146,C_147),D_146)
      | ~ r1_tarski(A_144,C_147)
      | ~ m1_subset_1(D_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145)))
      | ~ v1_funct_2(D_146,A_144,B_145)
      | ~ v1_funct_1(D_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1042,plain,(
    ! [C_147] :
      ( r2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',C_147),'#skF_4')
      | ~ r1_tarski(u1_struct_0('#skF_3'),C_147)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_329,c_1038])).

tff(c_1047,plain,(
    ! [C_148] :
      ( r2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',C_148),'#skF_4')
      | ~ r1_tarski(u1_struct_0('#skF_3'),C_148) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_330,c_1042])).

tff(c_10,plain,(
    ! [D_6,C_5,A_3,B_4] :
      ( D_6 = C_5
      | ~ r2_relset_1(A_3,B_4,C_5,D_6)
      | ~ m1_subset_1(D_6,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4)))
      | ~ m1_subset_1(C_5,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1049,plain,(
    ! [C_148] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',C_148) = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
      | ~ m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',C_148),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
      | ~ r1_tarski(u1_struct_0('#skF_3'),C_148) ) ),
    inference(resolution,[status(thm)],[c_1047,c_10])).

tff(c_1053,plain,(
    ! [C_149] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',C_149) = '#skF_4'
      | ~ m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',C_149),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
      | ~ r1_tarski(u1_struct_0('#skF_3'),C_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_1049])).

tff(c_1057,plain,(
    ! [D_10] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',D_10) = '#skF_4'
      | ~ r1_tarski(u1_struct_0('#skF_3'),D_10)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12,c_1053])).

tff(c_1060,plain,(
    ! [D_10] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',D_10) = '#skF_4'
      | ~ r1_tarski(u1_struct_0('#skF_3'),D_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_329,c_1057])).

tff(c_1573,plain,
    ( k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_2') = '#skF_4'
    | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1565,c_1060])).

tff(c_1593,plain,(
    k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1573])).

tff(c_1604,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1593,c_1565])).

tff(c_1944,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1936,c_1604])).

tff(c_1982,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1944])).

tff(c_42,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_325,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_42])).

tff(c_2019,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1982,c_325])).

tff(c_4169,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_4166,c_2019])).

tff(c_4172,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_330,c_329,c_4169])).

tff(c_4174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1343,c_4172])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:42:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.02/2.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.02/2.15  
% 6.02/2.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.02/2.15  %$ r1_funct_2 > r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.02/2.15  
% 6.02/2.15  %Foreground sorts:
% 6.02/2.15  
% 6.02/2.15  
% 6.02/2.15  %Background operators:
% 6.02/2.15  
% 6.02/2.15  
% 6.02/2.15  %Foreground operators:
% 6.02/2.15  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.02/2.15  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 6.02/2.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.02/2.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.02/2.15  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.02/2.15  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 6.02/2.15  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.02/2.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.02/2.15  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.02/2.15  tff('#skF_2', type, '#skF_2': $i).
% 6.02/2.15  tff('#skF_3', type, '#skF_3': $i).
% 6.02/2.15  tff('#skF_1', type, '#skF_1': $i).
% 6.02/2.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.02/2.15  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.02/2.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.02/2.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.02/2.15  tff('#skF_4', type, '#skF_4': $i).
% 6.02/2.15  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 6.02/2.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.02/2.15  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.02/2.15  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 6.02/2.15  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.02/2.15  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 6.02/2.15  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.02/2.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.02/2.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.02/2.15  
% 6.02/2.17  tff(f_199, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_tmap_1)).
% 6.02/2.17  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.02/2.17  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 6.02/2.17  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 6.02/2.17  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 6.02/2.17  tff(f_152, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 6.02/2.17  tff(f_66, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 6.02/2.17  tff(f_166, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 6.02/2.17  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.02/2.17  tff(f_121, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => r1_funct_2(A, B, C, D, E, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r1_funct_2)).
% 6.02/2.17  tff(f_85, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 6.02/2.17  tff(f_148, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 6.02/2.17  tff(f_47, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 6.02/2.17  tff(f_57, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_funct_2)).
% 6.02/2.17  tff(f_39, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.02/2.17  tff(c_62, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_199])).
% 6.02/2.17  tff(c_20, plain, (![A_18]: (l1_struct_0(A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.02/2.17  tff(c_66, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_199])).
% 6.02/2.17  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_199])).
% 6.02/2.17  tff(c_56, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 6.02/2.17  tff(c_52, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 6.02/2.17  tff(c_72, plain, (![B_73, A_74]: (l1_pre_topc(B_73) | ~m1_pre_topc(B_73, A_74) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.02/2.17  tff(c_78, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_72])).
% 6.02/2.17  tff(c_82, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_78])).
% 6.02/2.17  tff(c_44, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_199])).
% 6.02/2.17  tff(c_134, plain, (![A_90, B_91]: (m1_pre_topc(A_90, g1_pre_topc(u1_struct_0(B_91), u1_pre_topc(B_91))) | ~m1_pre_topc(A_90, B_91) | ~l1_pre_topc(B_91) | ~l1_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.02/2.17  tff(c_150, plain, (![A_90]: (m1_pre_topc(A_90, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_90, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_90))), inference(superposition, [status(thm), theory('equality')], [c_44, c_134])).
% 6.02/2.17  tff(c_180, plain, (![A_94]: (m1_pre_topc(A_94, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_94, '#skF_2') | ~l1_pre_topc(A_94))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_150])).
% 6.02/2.17  tff(c_26, plain, (![B_25, A_23]: (m1_pre_topc(B_25, A_23) | ~m1_pre_topc(B_25, g1_pre_topc(u1_struct_0(A_23), u1_pre_topc(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.02/2.17  tff(c_186, plain, (![A_94]: (m1_pre_topc(A_94, '#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc(A_94, '#skF_2') | ~l1_pre_topc(A_94))), inference(resolution, [status(thm)], [c_180, c_26])).
% 6.02/2.17  tff(c_199, plain, (![A_95]: (m1_pre_topc(A_95, '#skF_3') | ~m1_pre_topc(A_95, '#skF_2') | ~l1_pre_topc(A_95))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_186])).
% 6.02/2.17  tff(c_209, plain, (m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_52, c_199])).
% 6.02/2.17  tff(c_216, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_209])).
% 6.02/2.17  tff(c_36, plain, (![A_50]: (m1_pre_topc(A_50, A_50) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.02/2.17  tff(c_206, plain, (m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_36, c_199])).
% 6.02/2.17  tff(c_213, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_206])).
% 6.02/2.17  tff(c_58, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 6.02/2.17  tff(c_90, plain, (![B_77, A_78]: (v2_pre_topc(B_77) | ~m1_pre_topc(B_77, A_78) | ~l1_pre_topc(A_78) | ~v2_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.02/2.17  tff(c_96, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_90])).
% 6.02/2.17  tff(c_100, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_96])).
% 6.02/2.17  tff(c_38, plain, (![B_55, C_57, A_51]: (r1_tarski(u1_struct_0(B_55), u1_struct_0(C_57)) | ~m1_pre_topc(B_55, C_57) | ~m1_pre_topc(C_57, A_51) | ~m1_pre_topc(B_55, A_51) | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_166])).
% 6.02/2.17  tff(c_238, plain, (![B_55]: (r1_tarski(u1_struct_0(B_55), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_55, '#skF_2') | ~m1_pre_topc(B_55, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_213, c_38])).
% 6.02/2.17  tff(c_250, plain, (![B_55]: (r1_tarski(u1_struct_0(B_55), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_55, '#skF_2') | ~m1_pre_topc(B_55, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_82, c_238])).
% 6.02/2.17  tff(c_261, plain, (![B_55]: (r1_tarski(u1_struct_0(B_55), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_55, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_216, c_38])).
% 6.02/2.17  tff(c_283, plain, (![B_99]: (r1_tarski(u1_struct_0(B_99), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_99, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_82, c_261])).
% 6.02/2.17  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.02/2.17  tff(c_295, plain, (![B_103]: (u1_struct_0(B_103)=u1_struct_0('#skF_3') | ~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0(B_103)) | ~m1_pre_topc(B_103, '#skF_3'))), inference(resolution, [status(thm)], [c_283, c_2])).
% 6.02/2.17  tff(c_303, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_250, c_295])).
% 6.02/2.17  tff(c_315, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_216, c_52, c_213, c_303])).
% 6.02/2.17  tff(c_48, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_199])).
% 6.02/2.17  tff(c_330, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_315, c_48])).
% 6.02/2.17  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_199])).
% 6.02/2.17  tff(c_329, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_315, c_46])).
% 6.02/2.17  tff(c_1247, plain, (![E_162, B_159, C_163, D_158, A_160, F_161]: (r1_funct_2(A_160, B_159, C_163, D_158, E_162, E_162) | ~m1_subset_1(F_161, k1_zfmisc_1(k2_zfmisc_1(C_163, D_158))) | ~v1_funct_2(F_161, C_163, D_158) | ~v1_funct_1(F_161) | ~m1_subset_1(E_162, k1_zfmisc_1(k2_zfmisc_1(A_160, B_159))) | ~v1_funct_2(E_162, A_160, B_159) | ~v1_funct_1(E_162) | v1_xboole_0(D_158) | v1_xboole_0(B_159))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.02/2.17  tff(c_1251, plain, (![A_160, B_159, E_162]: (r1_funct_2(A_160, B_159, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), E_162, E_162) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_162, k1_zfmisc_1(k2_zfmisc_1(A_160, B_159))) | ~v1_funct_2(E_162, A_160, B_159) | ~v1_funct_1(E_162) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_159))), inference(resolution, [status(thm)], [c_329, c_1247])).
% 6.02/2.17  tff(c_1255, plain, (![A_160, B_159, E_162]: (r1_funct_2(A_160, B_159, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), E_162, E_162) | ~m1_subset_1(E_162, k1_zfmisc_1(k2_zfmisc_1(A_160, B_159))) | ~v1_funct_2(E_162, A_160, B_159) | ~v1_funct_1(E_162) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_159))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_330, c_1251])).
% 6.02/2.17  tff(c_1328, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_1255])).
% 6.02/2.17  tff(c_24, plain, (![A_22]: (~v1_xboole_0(u1_struct_0(A_22)) | ~l1_struct_0(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.02/2.17  tff(c_1331, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1328, c_24])).
% 6.02/2.17  tff(c_1334, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_66, c_1331])).
% 6.02/2.17  tff(c_1337, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_1334])).
% 6.02/2.17  tff(c_1341, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_1337])).
% 6.02/2.17  tff(c_1343, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_1255])).
% 6.02/2.17  tff(c_4166, plain, (![A_331, B_332, E_333]: (r1_funct_2(A_331, B_332, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), E_333, E_333) | ~m1_subset_1(E_333, k1_zfmisc_1(k2_zfmisc_1(A_331, B_332))) | ~v1_funct_2(E_333, A_331, B_332) | ~v1_funct_1(E_333) | v1_xboole_0(B_332))), inference(splitRight, [status(thm)], [c_1255])).
% 6.02/2.17  tff(c_64, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_199])).
% 6.02/2.17  tff(c_60, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_199])).
% 6.02/2.17  tff(c_1433, plain, (![A_170, B_171, C_172, D_173]: (k2_partfun1(u1_struct_0(A_170), u1_struct_0(B_171), C_172, u1_struct_0(D_173))=k2_tmap_1(A_170, B_171, C_172, D_173) | ~m1_pre_topc(D_173, A_170) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_170), u1_struct_0(B_171)))) | ~v1_funct_2(C_172, u1_struct_0(A_170), u1_struct_0(B_171)) | ~v1_funct_1(C_172) | ~l1_pre_topc(B_171) | ~v2_pre_topc(B_171) | v2_struct_0(B_171) | ~l1_pre_topc(A_170) | ~v2_pre_topc(A_170) | v2_struct_0(A_170))), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.02/2.17  tff(c_1440, plain, (![B_171, C_172, D_173]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_171), C_172, u1_struct_0(D_173))=k2_tmap_1('#skF_2', B_171, C_172, D_173) | ~m1_pre_topc(D_173, '#skF_2') | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_171)))) | ~v1_funct_2(C_172, u1_struct_0('#skF_2'), u1_struct_0(B_171)) | ~v1_funct_1(C_172) | ~l1_pre_topc(B_171) | ~v2_pre_topc(B_171) | v2_struct_0(B_171) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_315, c_1433])).
% 6.02/2.17  tff(c_1449, plain, (![B_171, C_172, D_173]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_171), C_172, u1_struct_0(D_173))=k2_tmap_1('#skF_2', B_171, C_172, D_173) | ~m1_pre_topc(D_173, '#skF_2') | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_171)))) | ~v1_funct_2(C_172, u1_struct_0('#skF_3'), u1_struct_0(B_171)) | ~v1_funct_1(C_172) | ~l1_pre_topc(B_171) | ~v2_pre_topc(B_171) | v2_struct_0(B_171) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_315, c_315, c_1440])).
% 6.02/2.17  tff(c_1908, plain, (![B_202, C_203, D_204]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_202), C_203, u1_struct_0(D_204))=k2_tmap_1('#skF_2', B_202, C_203, D_204) | ~m1_pre_topc(D_204, '#skF_2') | ~m1_subset_1(C_203, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_202)))) | ~v1_funct_2(C_203, u1_struct_0('#skF_3'), u1_struct_0(B_202)) | ~v1_funct_1(C_203) | ~l1_pre_topc(B_202) | ~v2_pre_topc(B_202) | v2_struct_0(B_202))), inference(negUnitSimplification, [status(thm)], [c_60, c_1449])).
% 6.02/2.17  tff(c_1915, plain, (![D_204]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_204))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_204) | ~m1_pre_topc(D_204, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_329, c_1908])).
% 6.02/2.17  tff(c_1925, plain, (![D_204]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_204))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_204) | ~m1_pre_topc(D_204, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_50, c_330, c_1915])).
% 6.02/2.17  tff(c_1936, plain, (![D_205]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_205))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_205) | ~m1_pre_topc(D_205, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_66, c_1925])).
% 6.02/2.17  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.02/2.17  tff(c_54, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_199])).
% 6.02/2.17  tff(c_1438, plain, (![D_173]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_173))=k2_tmap_1('#skF_3', '#skF_1', '#skF_4', D_173) | ~m1_pre_topc(D_173, '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_329, c_1433])).
% 6.02/2.17  tff(c_1446, plain, (![D_173]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_173))=k2_tmap_1('#skF_3', '#skF_1', '#skF_4', D_173) | ~m1_pre_topc(D_173, '#skF_3') | v2_struct_0('#skF_1') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_82, c_64, c_62, c_50, c_330, c_1438])).
% 6.02/2.17  tff(c_1536, plain, (![D_176]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_176))=k2_tmap_1('#skF_3', '#skF_1', '#skF_4', D_176) | ~m1_pre_topc(D_176, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_54, c_66, c_1446])).
% 6.02/2.17  tff(c_1559, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0('#skF_3'))=k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_315, c_1536])).
% 6.02/2.17  tff(c_1565, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0('#skF_3'))=k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_213, c_1559])).
% 6.02/2.17  tff(c_12, plain, (![A_7, B_8, C_9, D_10]: (m1_subset_1(k2_partfun1(A_7, B_8, C_9, D_10), k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))) | ~v1_funct_1(C_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.02/2.17  tff(c_1038, plain, (![A_144, B_145, D_146, C_147]: (r2_relset_1(A_144, B_145, k2_partfun1(A_144, B_145, D_146, C_147), D_146) | ~r1_tarski(A_144, C_147) | ~m1_subset_1(D_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))) | ~v1_funct_2(D_146, A_144, B_145) | ~v1_funct_1(D_146))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.02/2.17  tff(c_1042, plain, (![C_147]: (r2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', C_147), '#skF_4') | ~r1_tarski(u1_struct_0('#skF_3'), C_147) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_329, c_1038])).
% 6.02/2.17  tff(c_1047, plain, (![C_148]: (r2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', C_148), '#skF_4') | ~r1_tarski(u1_struct_0('#skF_3'), C_148))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_330, c_1042])).
% 6.02/2.17  tff(c_10, plain, (![D_6, C_5, A_3, B_4]: (D_6=C_5 | ~r2_relset_1(A_3, B_4, C_5, D_6) | ~m1_subset_1(D_6, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))) | ~m1_subset_1(C_5, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.02/2.17  tff(c_1049, plain, (![C_148]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', C_148)='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', C_148), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~r1_tarski(u1_struct_0('#skF_3'), C_148))), inference(resolution, [status(thm)], [c_1047, c_10])).
% 6.02/2.17  tff(c_1053, plain, (![C_149]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', C_149)='#skF_4' | ~m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', C_149), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~r1_tarski(u1_struct_0('#skF_3'), C_149))), inference(demodulation, [status(thm), theory('equality')], [c_329, c_1049])).
% 6.02/2.17  tff(c_1057, plain, (![D_10]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', D_10)='#skF_4' | ~r1_tarski(u1_struct_0('#skF_3'), D_10) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_12, c_1053])).
% 6.02/2.17  tff(c_1060, plain, (![D_10]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', D_10)='#skF_4' | ~r1_tarski(u1_struct_0('#skF_3'), D_10))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_329, c_1057])).
% 6.02/2.17  tff(c_1573, plain, (k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_2')='#skF_4' | ~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1565, c_1060])).
% 6.02/2.17  tff(c_1593, plain, (k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1573])).
% 6.02/2.17  tff(c_1604, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1593, c_1565])).
% 6.02/2.17  tff(c_1944, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1936, c_1604])).
% 6.02/2.17  tff(c_1982, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1944])).
% 6.02/2.17  tff(c_42, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_199])).
% 6.02/2.17  tff(c_325, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_315, c_42])).
% 6.02/2.17  tff(c_2019, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1982, c_325])).
% 6.02/2.17  tff(c_4169, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_4166, c_2019])).
% 6.02/2.17  tff(c_4172, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_330, c_329, c_4169])).
% 6.02/2.17  tff(c_4174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1343, c_4172])).
% 6.02/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.02/2.17  
% 6.02/2.17  Inference rules
% 6.02/2.17  ----------------------
% 6.02/2.17  #Ref     : 0
% 6.02/2.17  #Sup     : 843
% 6.02/2.17  #Fact    : 0
% 6.02/2.17  #Define  : 0
% 6.02/2.17  #Split   : 4
% 6.02/2.17  #Chain   : 0
% 6.02/2.17  #Close   : 0
% 6.02/2.17  
% 6.02/2.17  Ordering : KBO
% 6.02/2.17  
% 6.02/2.17  Simplification rules
% 6.02/2.17  ----------------------
% 6.02/2.17  #Subsume      : 236
% 6.02/2.17  #Demod        : 1567
% 6.02/2.17  #Tautology    : 318
% 6.02/2.17  #SimpNegUnit  : 46
% 6.02/2.17  #BackRed      : 10
% 6.02/2.17  
% 6.02/2.17  #Partial instantiations: 0
% 6.02/2.17  #Strategies tried      : 1
% 6.02/2.17  
% 6.02/2.17  Timing (in seconds)
% 6.02/2.17  ----------------------
% 6.02/2.17  Preprocessing        : 0.35
% 6.02/2.17  Parsing              : 0.19
% 6.02/2.17  CNF conversion       : 0.03
% 6.02/2.17  Main loop            : 1.05
% 6.02/2.17  Inferencing          : 0.35
% 6.02/2.17  Reduction            : 0.36
% 6.02/2.17  Demodulation         : 0.27
% 6.02/2.18  BG Simplification    : 0.04
% 6.02/2.18  Subsumption          : 0.25
% 6.02/2.18  Abstraction          : 0.05
% 6.02/2.18  MUC search           : 0.00
% 6.02/2.18  Cooper               : 0.00
% 6.02/2.18  Total                : 1.44
% 6.02/2.18  Index Insertion      : 0.00
% 6.02/2.18  Index Deletion       : 0.00
% 6.02/2.18  Index Matching       : 0.00
% 6.02/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
