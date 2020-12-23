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
% DateTime   : Thu Dec  3 10:26:56 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 391 expanded)
%              Number of leaves         :   43 ( 141 expanded)
%              Depth                    :   15
%              Number of atoms          :  278 (1475 expanded)
%              Number of equality atoms :   36 ( 304 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_165,negated_conjecture,(
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

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_105,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).

tff(f_76,axiom,(
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

tff(f_132,axiom,(
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

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_16,plain,(
    ! [A_18] :
      ( l1_struct_0(A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_42,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_65,plain,(
    ! [B_68,A_69] :
      ( l1_pre_topc(B_68)
      | ~ m1_pre_topc(B_68,A_69)
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_68,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_65])).

tff(c_71,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_68])).

tff(c_96,plain,(
    ! [A_76] :
      ( m1_subset_1(u1_pre_topc(A_76),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_76))))
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_100,plain,(
    ! [A_76] :
      ( r1_tarski(u1_pre_topc(A_76),k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(resolution,[status(thm)],[c_96,c_2])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_34,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_183,plain,(
    ! [C_96,A_97,D_98,B_99] :
      ( C_96 = A_97
      | g1_pre_topc(C_96,D_98) != g1_pre_topc(A_97,B_99)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(k1_zfmisc_1(A_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_221,plain,(
    ! [A_111,B_112] :
      ( u1_struct_0('#skF_2') = A_111
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(A_111,B_112)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(k1_zfmisc_1(A_111))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_183])).

tff(c_235,plain,(
    ! [A_111,A_1] :
      ( u1_struct_0('#skF_2') = A_111
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(A_111,A_1)
      | ~ r1_tarski(A_1,k1_zfmisc_1(A_111)) ) ),
    inference(resolution,[status(thm)],[c_4,c_221])).

tff(c_238,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ r1_tarski(u1_pre_topc('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_235])).

tff(c_244,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_238])).

tff(c_247,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_244])).

tff(c_251,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_247])).

tff(c_252,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_238])).

tff(c_38,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_264,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_38])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_263,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_36])).

tff(c_28,plain,(
    ! [D_33,A_30,C_32,B_31,E_34,F_35] :
      ( r1_funct_2(A_30,B_31,C_32,D_33,E_34,E_34)
      | ~ m1_subset_1(F_35,k1_zfmisc_1(k2_zfmisc_1(C_32,D_33)))
      | ~ v1_funct_2(F_35,C_32,D_33)
      | ~ v1_funct_1(F_35)
      | ~ m1_subset_1(E_34,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | ~ v1_funct_2(E_34,A_30,B_31)
      | ~ v1_funct_1(E_34)
      | v1_xboole_0(D_33)
      | v1_xboole_0(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_337,plain,(
    ! [A_30,B_31,E_34] :
      ( r1_funct_2(A_30,B_31,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),E_34,E_34)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_34,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | ~ v1_funct_2(E_34,A_30,B_31)
      | ~ v1_funct_1(E_34)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_31) ) ),
    inference(resolution,[status(thm)],[c_263,c_28])).

tff(c_353,plain,(
    ! [A_30,B_31,E_34] :
      ( r1_funct_2(A_30,B_31,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),E_34,E_34)
      | ~ m1_subset_1(E_34,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | ~ v1_funct_2(E_34,A_30,B_31)
      | ~ v1_funct_1(E_34)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_264,c_337])).

tff(c_557,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_353])).

tff(c_22,plain,(
    ! [A_23] :
      ( ~ v1_xboole_0(u1_struct_0(A_23))
      | ~ l1_struct_0(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_560,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_557,c_22])).

tff(c_563,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_560])).

tff(c_575,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_563])).

tff(c_579,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_575])).

tff(c_581,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_353])).

tff(c_75,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_36,c_2])).

tff(c_262,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_75])).

tff(c_318,plain,(
    ! [A_122,F_121,B_120,C_119,E_123,D_124] :
      ( r1_funct_2(A_122,B_120,C_119,D_124,E_123,E_123)
      | ~ m1_subset_1(F_121,k1_zfmisc_1(k2_zfmisc_1(C_119,D_124)))
      | ~ v1_funct_2(F_121,C_119,D_124)
      | ~ v1_funct_1(F_121)
      | ~ m1_subset_1(E_123,k1_zfmisc_1(k2_zfmisc_1(A_122,B_120)))
      | ~ v1_funct_2(E_123,A_122,B_120)
      | ~ v1_funct_1(E_123)
      | v1_xboole_0(D_124)
      | v1_xboole_0(B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_619,plain,(
    ! [C_187,B_188,A_190,A_192,E_189,D_191] :
      ( r1_funct_2(A_190,B_188,C_187,D_191,E_189,E_189)
      | ~ v1_funct_2(A_192,C_187,D_191)
      | ~ v1_funct_1(A_192)
      | ~ m1_subset_1(E_189,k1_zfmisc_1(k2_zfmisc_1(A_190,B_188)))
      | ~ v1_funct_2(E_189,A_190,B_188)
      | ~ v1_funct_1(E_189)
      | v1_xboole_0(D_191)
      | v1_xboole_0(B_188)
      | ~ r1_tarski(A_192,k2_zfmisc_1(C_187,D_191)) ) ),
    inference(resolution,[status(thm)],[c_4,c_318])).

tff(c_621,plain,(
    ! [C_187,D_191,A_192] :
      ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),C_187,D_191,'#skF_4','#skF_4')
      | ~ v1_funct_2(A_192,C_187,D_191)
      | ~ v1_funct_1(A_192)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(D_191)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_192,k2_zfmisc_1(C_187,D_191)) ) ),
    inference(resolution,[status(thm)],[c_263,c_619])).

tff(c_630,plain,(
    ! [C_187,D_191,A_192] :
      ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),C_187,D_191,'#skF_4','#skF_4')
      | ~ v1_funct_2(A_192,C_187,D_191)
      | ~ v1_funct_1(A_192)
      | v1_xboole_0(D_191)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_192,k2_zfmisc_1(C_187,D_191)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_264,c_621])).

tff(c_634,plain,(
    ! [C_193,D_194,A_195] :
      ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),C_193,D_194,'#skF_4','#skF_4')
      | ~ v1_funct_2(A_195,C_193,D_194)
      | ~ v1_funct_1(A_195)
      | v1_xboole_0(D_194)
      | ~ r1_tarski(A_195,k2_zfmisc_1(C_193,D_194)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_581,c_630])).

tff(c_639,plain,
    ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_262,c_634])).

tff(c_646,plain,
    ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_264,c_639])).

tff(c_647,plain,(
    r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_581,c_646])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_14,plain,(
    ! [A_14,B_15,C_16,D_17] :
      ( k2_partfun1(A_14,B_15,C_16,D_17) = k7_relat_1(C_16,D_17)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15)))
      | ~ v1_funct_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_339,plain,(
    ! [D_17] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',D_17) = k7_relat_1('#skF_4',D_17)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_263,c_14])).

tff(c_356,plain,(
    ! [D_17] : k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',D_17) = k7_relat_1('#skF_4',D_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_339])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_385,plain,(
    ! [A_125,B_126,C_127,D_128] :
      ( k2_partfun1(u1_struct_0(A_125),u1_struct_0(B_126),C_127,u1_struct_0(D_128)) = k2_tmap_1(A_125,B_126,C_127,D_128)
      | ~ m1_pre_topc(D_128,A_125)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_125),u1_struct_0(B_126))))
      | ~ v1_funct_2(C_127,u1_struct_0(A_125),u1_struct_0(B_126))
      | ~ v1_funct_1(C_127)
      | ~ l1_pre_topc(B_126)
      | ~ v2_pre_topc(B_126)
      | v2_struct_0(B_126)
      | ~ l1_pre_topc(A_125)
      | ~ v2_pre_topc(A_125)
      | v2_struct_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_649,plain,(
    ! [A_196,B_197,A_198,D_199] :
      ( k2_partfun1(u1_struct_0(A_196),u1_struct_0(B_197),A_198,u1_struct_0(D_199)) = k2_tmap_1(A_196,B_197,A_198,D_199)
      | ~ m1_pre_topc(D_199,A_196)
      | ~ v1_funct_2(A_198,u1_struct_0(A_196),u1_struct_0(B_197))
      | ~ v1_funct_1(A_198)
      | ~ l1_pre_topc(B_197)
      | ~ v2_pre_topc(B_197)
      | v2_struct_0(B_197)
      | ~ l1_pre_topc(A_196)
      | ~ v2_pre_topc(A_196)
      | v2_struct_0(A_196)
      | ~ r1_tarski(A_198,k2_zfmisc_1(u1_struct_0(A_196),u1_struct_0(B_197))) ) ),
    inference(resolution,[status(thm)],[c_4,c_385])).

tff(c_656,plain,(
    ! [B_197,A_198,D_199] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0(B_197),A_198,u1_struct_0(D_199)) = k2_tmap_1('#skF_2',B_197,A_198,D_199)
      | ~ m1_pre_topc(D_199,'#skF_2')
      | ~ v1_funct_2(A_198,u1_struct_0('#skF_2'),u1_struct_0(B_197))
      | ~ v1_funct_1(A_198)
      | ~ l1_pre_topc(B_197)
      | ~ v2_pre_topc(B_197)
      | v2_struct_0(B_197)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_198,k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_197))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_649])).

tff(c_668,plain,(
    ! [B_197,A_198,D_199] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_197),A_198,u1_struct_0(D_199)) = k2_tmap_1('#skF_2',B_197,A_198,D_199)
      | ~ m1_pre_topc(D_199,'#skF_2')
      | ~ v1_funct_2(A_198,u1_struct_0('#skF_3'),u1_struct_0(B_197))
      | ~ v1_funct_1(A_198)
      | ~ l1_pre_topc(B_197)
      | ~ v2_pre_topc(B_197)
      | v2_struct_0(B_197)
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_198,k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_197))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_252,c_252,c_656])).

tff(c_690,plain,(
    ! [B_209,A_210,D_211] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_209),A_210,u1_struct_0(D_211)) = k2_tmap_1('#skF_2',B_209,A_210,D_211)
      | ~ m1_pre_topc(D_211,'#skF_2')
      | ~ v1_funct_2(A_210,u1_struct_0('#skF_3'),u1_struct_0(B_209))
      | ~ v1_funct_1(A_210)
      | ~ l1_pre_topc(B_209)
      | ~ v2_pre_topc(B_209)
      | v2_struct_0(B_209)
      | ~ r1_tarski(A_210,k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_209))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_668])).

tff(c_695,plain,(
    ! [D_211] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_211)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_211)
      | ~ m1_pre_topc(D_211,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_262,c_690])).

tff(c_704,plain,(
    ! [D_211] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_211)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_211)
      | ~ m1_pre_topc(D_211,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_40,c_264,c_356,c_695])).

tff(c_710,plain,(
    ! [D_212] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_212)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_212)
      | ~ m1_pre_topc(D_212,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_704])).

tff(c_76,plain,(
    ! [C_70,A_71,B_72] :
      ( v1_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_84,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_76])).

tff(c_103,plain,(
    ! [A_80,B_81,C_82] :
      ( k1_relset_1(A_80,B_81,C_82) = k1_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_111,plain,(
    k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_103])).

tff(c_132,plain,(
    ! [A_90,B_91,C_92] :
      ( m1_subset_1(k1_relset_1(A_90,B_91,C_92),k1_zfmisc_1(A_90))
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_146,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_132])).

tff(c_151,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_146])).

tff(c_155,plain,(
    r1_tarski(k1_relat_1('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_151,c_2])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k7_relat_1(B_4,A_3) = B_4
      | ~ r1_tarski(k1_relat_1(B_4),A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_158,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_155,c_6])).

tff(c_161,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_158])).

tff(c_256,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_161])).

tff(c_716,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_710,c_256])).

tff(c_728,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_716])).

tff(c_32,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_259,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_32])).

tff(c_733,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_728,c_259])).

tff(c_736,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_647,c_733])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:45:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.48  
% 3.06/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.48  %$ r1_funct_2 > v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.06/1.48  
% 3.06/1.48  %Foreground sorts:
% 3.06/1.48  
% 3.06/1.48  
% 3.06/1.48  %Background operators:
% 3.06/1.48  
% 3.06/1.48  
% 3.06/1.48  %Foreground operators:
% 3.06/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.06/1.48  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.06/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.06/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.06/1.48  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.06/1.48  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.06/1.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.06/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.06/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.06/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.06/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.06/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.06/1.48  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.06/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.06/1.48  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.06/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.06/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.06/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.06/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.06/1.48  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 3.06/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.06/1.48  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.06/1.48  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.06/1.48  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.06/1.48  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.06/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.06/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.06/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.06/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.06/1.48  
% 3.06/1.50  tff(f_165, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_tmap_1)).
% 3.06/1.50  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.06/1.50  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.06/1.50  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 3.06/1.50  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.06/1.50  tff(f_85, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 3.06/1.50  tff(f_105, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => r1_funct_2(A, B, C, D, E, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r1_funct_2)).
% 3.06/1.50  tff(f_76, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.06/1.50  tff(f_53, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.06/1.50  tff(f_132, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.06/1.50  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.06/1.50  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.06/1.50  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.06/1.50  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 3.06/1.50  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.06/1.50  tff(c_16, plain, (![A_18]: (l1_struct_0(A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.06/1.50  tff(c_56, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.06/1.50  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.06/1.50  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.06/1.50  tff(c_42, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.06/1.50  tff(c_65, plain, (![B_68, A_69]: (l1_pre_topc(B_68) | ~m1_pre_topc(B_68, A_69) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.06/1.50  tff(c_68, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_65])).
% 3.06/1.50  tff(c_71, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_68])).
% 3.06/1.50  tff(c_96, plain, (![A_76]: (m1_subset_1(u1_pre_topc(A_76), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_76)))) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.06/1.50  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.06/1.50  tff(c_100, plain, (![A_76]: (r1_tarski(u1_pre_topc(A_76), k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76))), inference(resolution, [status(thm)], [c_96, c_2])).
% 3.06/1.50  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.06/1.50  tff(c_34, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.06/1.50  tff(c_183, plain, (![C_96, A_97, D_98, B_99]: (C_96=A_97 | g1_pre_topc(C_96, D_98)!=g1_pre_topc(A_97, B_99) | ~m1_subset_1(B_99, k1_zfmisc_1(k1_zfmisc_1(A_97))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.06/1.50  tff(c_221, plain, (![A_111, B_112]: (u1_struct_0('#skF_2')=A_111 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(A_111, B_112) | ~m1_subset_1(B_112, k1_zfmisc_1(k1_zfmisc_1(A_111))))), inference(superposition, [status(thm), theory('equality')], [c_34, c_183])).
% 3.06/1.50  tff(c_235, plain, (![A_111, A_1]: (u1_struct_0('#skF_2')=A_111 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(A_111, A_1) | ~r1_tarski(A_1, k1_zfmisc_1(A_111)))), inference(resolution, [status(thm)], [c_4, c_221])).
% 3.06/1.50  tff(c_238, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~r1_tarski(u1_pre_topc('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(reflexivity, [status(thm), theory('equality')], [c_235])).
% 3.06/1.50  tff(c_244, plain, (~r1_tarski(u1_pre_topc('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_238])).
% 3.06/1.50  tff(c_247, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_100, c_244])).
% 3.06/1.50  tff(c_251, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_247])).
% 3.06/1.50  tff(c_252, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_238])).
% 3.06/1.50  tff(c_38, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.06/1.50  tff(c_264, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_252, c_38])).
% 3.06/1.50  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.06/1.50  tff(c_263, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_252, c_36])).
% 3.06/1.50  tff(c_28, plain, (![D_33, A_30, C_32, B_31, E_34, F_35]: (r1_funct_2(A_30, B_31, C_32, D_33, E_34, E_34) | ~m1_subset_1(F_35, k1_zfmisc_1(k2_zfmisc_1(C_32, D_33))) | ~v1_funct_2(F_35, C_32, D_33) | ~v1_funct_1(F_35) | ~m1_subset_1(E_34, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | ~v1_funct_2(E_34, A_30, B_31) | ~v1_funct_1(E_34) | v1_xboole_0(D_33) | v1_xboole_0(B_31))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.06/1.50  tff(c_337, plain, (![A_30, B_31, E_34]: (r1_funct_2(A_30, B_31, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), E_34, E_34) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_34, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | ~v1_funct_2(E_34, A_30, B_31) | ~v1_funct_1(E_34) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_31))), inference(resolution, [status(thm)], [c_263, c_28])).
% 3.06/1.50  tff(c_353, plain, (![A_30, B_31, E_34]: (r1_funct_2(A_30, B_31, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), E_34, E_34) | ~m1_subset_1(E_34, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | ~v1_funct_2(E_34, A_30, B_31) | ~v1_funct_1(E_34) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_31))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_264, c_337])).
% 3.06/1.50  tff(c_557, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_353])).
% 3.06/1.50  tff(c_22, plain, (![A_23]: (~v1_xboole_0(u1_struct_0(A_23)) | ~l1_struct_0(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.06/1.50  tff(c_560, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_557, c_22])).
% 3.06/1.50  tff(c_563, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_56, c_560])).
% 3.06/1.50  tff(c_575, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_563])).
% 3.06/1.50  tff(c_579, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_575])).
% 3.06/1.50  tff(c_581, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_353])).
% 3.06/1.50  tff(c_75, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_36, c_2])).
% 3.06/1.50  tff(c_262, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_252, c_75])).
% 3.06/1.50  tff(c_318, plain, (![A_122, F_121, B_120, C_119, E_123, D_124]: (r1_funct_2(A_122, B_120, C_119, D_124, E_123, E_123) | ~m1_subset_1(F_121, k1_zfmisc_1(k2_zfmisc_1(C_119, D_124))) | ~v1_funct_2(F_121, C_119, D_124) | ~v1_funct_1(F_121) | ~m1_subset_1(E_123, k1_zfmisc_1(k2_zfmisc_1(A_122, B_120))) | ~v1_funct_2(E_123, A_122, B_120) | ~v1_funct_1(E_123) | v1_xboole_0(D_124) | v1_xboole_0(B_120))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.06/1.50  tff(c_619, plain, (![C_187, B_188, A_190, A_192, E_189, D_191]: (r1_funct_2(A_190, B_188, C_187, D_191, E_189, E_189) | ~v1_funct_2(A_192, C_187, D_191) | ~v1_funct_1(A_192) | ~m1_subset_1(E_189, k1_zfmisc_1(k2_zfmisc_1(A_190, B_188))) | ~v1_funct_2(E_189, A_190, B_188) | ~v1_funct_1(E_189) | v1_xboole_0(D_191) | v1_xboole_0(B_188) | ~r1_tarski(A_192, k2_zfmisc_1(C_187, D_191)))), inference(resolution, [status(thm)], [c_4, c_318])).
% 3.06/1.50  tff(c_621, plain, (![C_187, D_191, A_192]: (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), C_187, D_191, '#skF_4', '#skF_4') | ~v1_funct_2(A_192, C_187, D_191) | ~v1_funct_1(A_192) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(D_191) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski(A_192, k2_zfmisc_1(C_187, D_191)))), inference(resolution, [status(thm)], [c_263, c_619])).
% 3.06/1.50  tff(c_630, plain, (![C_187, D_191, A_192]: (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), C_187, D_191, '#skF_4', '#skF_4') | ~v1_funct_2(A_192, C_187, D_191) | ~v1_funct_1(A_192) | v1_xboole_0(D_191) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski(A_192, k2_zfmisc_1(C_187, D_191)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_264, c_621])).
% 3.06/1.50  tff(c_634, plain, (![C_193, D_194, A_195]: (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), C_193, D_194, '#skF_4', '#skF_4') | ~v1_funct_2(A_195, C_193, D_194) | ~v1_funct_1(A_195) | v1_xboole_0(D_194) | ~r1_tarski(A_195, k2_zfmisc_1(C_193, D_194)))), inference(negUnitSimplification, [status(thm)], [c_581, c_630])).
% 3.06/1.50  tff(c_639, plain, (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_262, c_634])).
% 3.06/1.50  tff(c_646, plain, (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_264, c_639])).
% 3.06/1.50  tff(c_647, plain, (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_581, c_646])).
% 3.06/1.50  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.06/1.50  tff(c_14, plain, (![A_14, B_15, C_16, D_17]: (k2_partfun1(A_14, B_15, C_16, D_17)=k7_relat_1(C_16, D_17) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))) | ~v1_funct_1(C_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.06/1.50  tff(c_339, plain, (![D_17]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', D_17)=k7_relat_1('#skF_4', D_17) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_263, c_14])).
% 3.06/1.50  tff(c_356, plain, (![D_17]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', D_17)=k7_relat_1('#skF_4', D_17))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_339])).
% 3.06/1.50  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.06/1.50  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.06/1.50  tff(c_385, plain, (![A_125, B_126, C_127, D_128]: (k2_partfun1(u1_struct_0(A_125), u1_struct_0(B_126), C_127, u1_struct_0(D_128))=k2_tmap_1(A_125, B_126, C_127, D_128) | ~m1_pre_topc(D_128, A_125) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_125), u1_struct_0(B_126)))) | ~v1_funct_2(C_127, u1_struct_0(A_125), u1_struct_0(B_126)) | ~v1_funct_1(C_127) | ~l1_pre_topc(B_126) | ~v2_pre_topc(B_126) | v2_struct_0(B_126) | ~l1_pre_topc(A_125) | ~v2_pre_topc(A_125) | v2_struct_0(A_125))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.06/1.50  tff(c_649, plain, (![A_196, B_197, A_198, D_199]: (k2_partfun1(u1_struct_0(A_196), u1_struct_0(B_197), A_198, u1_struct_0(D_199))=k2_tmap_1(A_196, B_197, A_198, D_199) | ~m1_pre_topc(D_199, A_196) | ~v1_funct_2(A_198, u1_struct_0(A_196), u1_struct_0(B_197)) | ~v1_funct_1(A_198) | ~l1_pre_topc(B_197) | ~v2_pre_topc(B_197) | v2_struct_0(B_197) | ~l1_pre_topc(A_196) | ~v2_pre_topc(A_196) | v2_struct_0(A_196) | ~r1_tarski(A_198, k2_zfmisc_1(u1_struct_0(A_196), u1_struct_0(B_197))))), inference(resolution, [status(thm)], [c_4, c_385])).
% 3.06/1.50  tff(c_656, plain, (![B_197, A_198, D_199]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_197), A_198, u1_struct_0(D_199))=k2_tmap_1('#skF_2', B_197, A_198, D_199) | ~m1_pre_topc(D_199, '#skF_2') | ~v1_funct_2(A_198, u1_struct_0('#skF_2'), u1_struct_0(B_197)) | ~v1_funct_1(A_198) | ~l1_pre_topc(B_197) | ~v2_pre_topc(B_197) | v2_struct_0(B_197) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(A_198, k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_197))))), inference(superposition, [status(thm), theory('equality')], [c_252, c_649])).
% 3.06/1.50  tff(c_668, plain, (![B_197, A_198, D_199]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_197), A_198, u1_struct_0(D_199))=k2_tmap_1('#skF_2', B_197, A_198, D_199) | ~m1_pre_topc(D_199, '#skF_2') | ~v1_funct_2(A_198, u1_struct_0('#skF_3'), u1_struct_0(B_197)) | ~v1_funct_1(A_198) | ~l1_pre_topc(B_197) | ~v2_pre_topc(B_197) | v2_struct_0(B_197) | v2_struct_0('#skF_2') | ~r1_tarski(A_198, k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_197))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_252, c_252, c_656])).
% 3.06/1.50  tff(c_690, plain, (![B_209, A_210, D_211]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_209), A_210, u1_struct_0(D_211))=k2_tmap_1('#skF_2', B_209, A_210, D_211) | ~m1_pre_topc(D_211, '#skF_2') | ~v1_funct_2(A_210, u1_struct_0('#skF_3'), u1_struct_0(B_209)) | ~v1_funct_1(A_210) | ~l1_pre_topc(B_209) | ~v2_pre_topc(B_209) | v2_struct_0(B_209) | ~r1_tarski(A_210, k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_209))))), inference(negUnitSimplification, [status(thm)], [c_50, c_668])).
% 3.06/1.50  tff(c_695, plain, (![D_211]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_211))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_211) | ~m1_pre_topc(D_211, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_262, c_690])).
% 3.06/1.50  tff(c_704, plain, (![D_211]: (k7_relat_1('#skF_4', u1_struct_0(D_211))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_211) | ~m1_pre_topc(D_211, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_40, c_264, c_356, c_695])).
% 3.06/1.50  tff(c_710, plain, (![D_212]: (k7_relat_1('#skF_4', u1_struct_0(D_212))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_212) | ~m1_pre_topc(D_212, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_704])).
% 3.06/1.50  tff(c_76, plain, (![C_70, A_71, B_72]: (v1_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.06/1.50  tff(c_84, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_76])).
% 3.06/1.50  tff(c_103, plain, (![A_80, B_81, C_82]: (k1_relset_1(A_80, B_81, C_82)=k1_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.06/1.50  tff(c_111, plain, (k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_103])).
% 3.06/1.50  tff(c_132, plain, (![A_90, B_91, C_92]: (m1_subset_1(k1_relset_1(A_90, B_91, C_92), k1_zfmisc_1(A_90)) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.06/1.50  tff(c_146, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_111, c_132])).
% 3.06/1.50  tff(c_151, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_146])).
% 3.06/1.50  tff(c_155, plain, (r1_tarski(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_151, c_2])).
% 3.06/1.50  tff(c_6, plain, (![B_4, A_3]: (k7_relat_1(B_4, A_3)=B_4 | ~r1_tarski(k1_relat_1(B_4), A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.06/1.50  tff(c_158, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_155, c_6])).
% 3.06/1.50  tff(c_161, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_158])).
% 3.06/1.50  tff(c_256, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_252, c_161])).
% 3.06/1.50  tff(c_716, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_710, c_256])).
% 3.06/1.50  tff(c_728, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_716])).
% 3.06/1.50  tff(c_32, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.06/1.50  tff(c_259, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_252, c_32])).
% 3.06/1.50  tff(c_733, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_728, c_259])).
% 3.06/1.50  tff(c_736, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_647, c_733])).
% 3.06/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.50  
% 3.06/1.50  Inference rules
% 3.06/1.50  ----------------------
% 3.06/1.50  #Ref     : 6
% 3.06/1.50  #Sup     : 135
% 3.06/1.50  #Fact    : 0
% 3.06/1.50  #Define  : 0
% 3.06/1.50  #Split   : 4
% 3.06/1.50  #Chain   : 0
% 3.06/1.50  #Close   : 0
% 3.06/1.50  
% 3.06/1.50  Ordering : KBO
% 3.06/1.50  
% 3.06/1.50  Simplification rules
% 3.06/1.50  ----------------------
% 3.06/1.50  #Subsume      : 16
% 3.06/1.50  #Demod        : 123
% 3.06/1.50  #Tautology    : 48
% 3.06/1.50  #SimpNegUnit  : 14
% 3.06/1.50  #BackRed      : 15
% 3.06/1.50  
% 3.06/1.50  #Partial instantiations: 0
% 3.06/1.50  #Strategies tried      : 1
% 3.06/1.50  
% 3.06/1.50  Timing (in seconds)
% 3.06/1.50  ----------------------
% 3.06/1.50  Preprocessing        : 0.33
% 3.06/1.50  Parsing              : 0.18
% 3.06/1.50  CNF conversion       : 0.02
% 3.06/1.50  Main loop            : 0.38
% 3.06/1.50  Inferencing          : 0.15
% 3.06/1.50  Reduction            : 0.11
% 3.06/1.50  Demodulation         : 0.08
% 3.06/1.50  BG Simplification    : 0.02
% 3.06/1.50  Subsumption          : 0.06
% 3.06/1.51  Abstraction          : 0.03
% 3.06/1.51  MUC search           : 0.00
% 3.06/1.51  Cooper               : 0.00
% 3.06/1.51  Total                : 0.76
% 3.06/1.51  Index Insertion      : 0.00
% 3.06/1.51  Index Deletion       : 0.00
% 3.06/1.51  Index Matching       : 0.00
% 3.06/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
