%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:57 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 687 expanded)
%              Number of leaves         :   37 ( 214 expanded)
%              Depth                    :   22
%              Number of atoms          :  233 (2657 expanded)
%              Number of equality atoms :   39 ( 889 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_164,negated_conjecture,(
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

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_82,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_104,axiom,(
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

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(A,C)
       => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_39,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_131,axiom,(
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

tff(c_54,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_18,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_42,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_20,plain,(
    ! [A_16] :
      ( m1_subset_1(u1_pre_topc(A_16),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_16))))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_36,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_83,plain,(
    ! [D_65,B_66,C_67,A_68] :
      ( D_65 = B_66
      | g1_pre_topc(C_67,D_65) != g1_pre_topc(A_68,B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(k1_zfmisc_1(A_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_87,plain,(
    ! [D_65,C_67] :
      ( u1_pre_topc('#skF_2') = D_65
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_67,D_65)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_83])).

tff(c_133,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_136,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_133])).

tff(c_140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_136])).

tff(c_141,plain,(
    ! [D_65,C_67] :
      ( u1_pre_topc('#skF_2') = D_65
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_67,D_65) ) ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_159,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_141])).

tff(c_142,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_174,plain,(
    m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_142])).

tff(c_175,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_3')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_36])).

tff(c_26,plain,(
    ! [C_22,A_18,D_23,B_19] :
      ( C_22 = A_18
      | g1_pre_topc(C_22,D_23) != g1_pre_topc(A_18,B_19)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(k1_zfmisc_1(A_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_195,plain,(
    ! [C_22,D_23] :
      ( u1_struct_0('#skF_2') = C_22
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_22,D_23)
      | ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_26])).

tff(c_203,plain,(
    ! [C_22,D_23] :
      ( u1_struct_0('#skF_2') = C_22
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_22,D_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_195])).

tff(c_218,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_203])).

tff(c_40,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_232,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_40])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_231,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_38])).

tff(c_282,plain,(
    ! [C_102,B_103,A_105,F_104,D_106] :
      ( r1_funct_2(A_105,B_103,C_102,D_106,F_104,F_104)
      | ~ m1_subset_1(F_104,k1_zfmisc_1(k2_zfmisc_1(C_102,D_106)))
      | ~ v1_funct_2(F_104,C_102,D_106)
      | ~ m1_subset_1(F_104,k1_zfmisc_1(k2_zfmisc_1(A_105,B_103)))
      | ~ v1_funct_2(F_104,A_105,B_103)
      | ~ v1_funct_1(F_104)
      | v1_xboole_0(D_106)
      | v1_xboole_0(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_284,plain,(
    ! [A_105,B_103] :
      ( r1_funct_2(A_105,B_103,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_105,B_103)))
      | ~ v1_funct_2('#skF_4',A_105,B_103)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_103) ) ),
    inference(resolution,[status(thm)],[c_231,c_282])).

tff(c_289,plain,(
    ! [A_105,B_103] :
      ( r1_funct_2(A_105,B_103,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_105,B_103)))
      | ~ v1_funct_2('#skF_4',A_105,B_103)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_232,c_284])).

tff(c_322,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_289])).

tff(c_22,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(u1_struct_0(A_17))
      | ~ l1_struct_0(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_325,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_322,c_22])).

tff(c_328,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_325])).

tff(c_331,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_328])).

tff(c_335,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_331])).

tff(c_337,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_289])).

tff(c_336,plain,(
    ! [A_105,B_103] :
      ( r1_funct_2(A_105,B_103,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_105,B_103)))
      | ~ v1_funct_2('#skF_4',A_105,B_103)
      | v1_xboole_0(B_103) ) ),
    inference(splitRight,[status(thm)],[c_289])).

tff(c_44,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9,D_10] :
      ( m1_subset_1(k2_partfun1(A_7,B_8,C_9,D_10),k1_zfmisc_1(k2_zfmisc_1(A_7,B_8)))
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8)))
      | ~ v1_funct_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [A_11,B_12,D_14,C_13] :
      ( r2_relset_1(A_11,B_12,k2_partfun1(A_11,B_12,D_14,C_13),D_14)
      | ~ r1_tarski(A_11,C_13)
      | ~ m1_subset_1(D_14,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12)))
      | ~ v1_funct_2(D_14,A_11,B_12)
      | ~ v1_funct_1(D_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_261,plain,(
    ! [C_13] :
      ( r2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',C_13),'#skF_4')
      | ~ r1_tarski(u1_struct_0('#skF_3'),C_13)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_231,c_16])).

tff(c_298,plain,(
    ! [C_109] :
      ( r2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',C_109),'#skF_4')
      | ~ r1_tarski(u1_struct_0('#skF_3'),C_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_232,c_261])).

tff(c_10,plain,(
    ! [D_6,C_5,A_3,B_4] :
      ( D_6 = C_5
      | ~ r2_relset_1(A_3,B_4,C_5,D_6)
      | ~ m1_subset_1(D_6,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4)))
      | ~ m1_subset_1(C_5,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_300,plain,(
    ! [C_109] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',C_109) = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
      | ~ m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',C_109),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
      | ~ r1_tarski(u1_struct_0('#skF_3'),C_109) ) ),
    inference(resolution,[status(thm)],[c_298,c_10])).

tff(c_346,plain,(
    ! [C_129] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',C_129) = '#skF_4'
      | ~ m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',C_129),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
      | ~ r1_tarski(u1_struct_0('#skF_3'),C_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_300])).

tff(c_350,plain,(
    ! [D_10] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',D_10) = '#skF_4'
      | ~ r1_tarski(u1_struct_0('#skF_3'),D_10)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12,c_346])).

tff(c_353,plain,(
    ! [D_10] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',D_10) = '#skF_4'
      | ~ r1_tarski(u1_struct_0('#skF_3'),D_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_231,c_350])).

tff(c_56,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_50,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_398,plain,(
    ! [A_132,B_133,C_134,D_135] :
      ( k2_partfun1(u1_struct_0(A_132),u1_struct_0(B_133),C_134,u1_struct_0(D_135)) = k2_tmap_1(A_132,B_133,C_134,D_135)
      | ~ m1_pre_topc(D_135,A_132)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_132),u1_struct_0(B_133))))
      | ~ v1_funct_2(C_134,u1_struct_0(A_132),u1_struct_0(B_133))
      | ~ v1_funct_1(C_134)
      | ~ l1_pre_topc(B_133)
      | ~ v2_pre_topc(B_133)
      | v2_struct_0(B_133)
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132)
      | v2_struct_0(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_402,plain,(
    ! [B_133,C_134,D_135] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0(B_133),C_134,u1_struct_0(D_135)) = k2_tmap_1('#skF_2',B_133,C_134,D_135)
      | ~ m1_pre_topc(D_135,'#skF_2')
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_133))))
      | ~ v1_funct_2(C_134,u1_struct_0('#skF_2'),u1_struct_0(B_133))
      | ~ v1_funct_1(C_134)
      | ~ l1_pre_topc(B_133)
      | ~ v2_pre_topc(B_133)
      | v2_struct_0(B_133)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_398])).

tff(c_413,plain,(
    ! [B_133,C_134,D_135] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_133),C_134,u1_struct_0(D_135)) = k2_tmap_1('#skF_2',B_133,C_134,D_135)
      | ~ m1_pre_topc(D_135,'#skF_2')
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_133))))
      | ~ v1_funct_2(C_134,u1_struct_0('#skF_3'),u1_struct_0(B_133))
      | ~ v1_funct_1(C_134)
      | ~ l1_pre_topc(B_133)
      | ~ v2_pre_topc(B_133)
      | v2_struct_0(B_133)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_218,c_218,c_402])).

tff(c_425,plain,(
    ! [B_142,C_143,D_144] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_142),C_143,u1_struct_0(D_144)) = k2_tmap_1('#skF_2',B_142,C_143,D_144)
      | ~ m1_pre_topc(D_144,'#skF_2')
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_142))))
      | ~ v1_funct_2(C_143,u1_struct_0('#skF_3'),u1_struct_0(B_142))
      | ~ v1_funct_1(C_143)
      | ~ l1_pre_topc(B_142)
      | ~ v2_pre_topc(B_142)
      | v2_struct_0(B_142) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_413])).

tff(c_427,plain,(
    ! [D_144] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_144)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_144)
      | ~ m1_pre_topc(D_144,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_231,c_425])).

tff(c_435,plain,(
    ! [D_144] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_144)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_144)
      | ~ m1_pre_topc(D_144,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_42,c_232,c_427])).

tff(c_441,plain,(
    ! [D_145] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_145)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_145)
      | ~ m1_pre_topc(D_145,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_435])).

tff(c_495,plain,(
    ! [D_149] :
      ( k2_tmap_1('#skF_2','#skF_1','#skF_4',D_149) = '#skF_4'
      | ~ m1_pre_topc(D_149,'#skF_2')
      | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0(D_149)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_353,c_441])).

tff(c_502,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_495])).

tff(c_507,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_502])).

tff(c_34,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_229,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_34])).

tff(c_508,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_507,c_229])).

tff(c_545,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_336,c_508])).

tff(c_548,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_231,c_545])).

tff(c_550,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_337,c_548])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:10:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.42  
% 2.92/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.42  %$ r1_funct_2 > r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.92/1.42  
% 2.92/1.42  %Foreground sorts:
% 2.92/1.42  
% 2.92/1.42  
% 2.92/1.42  %Background operators:
% 2.92/1.42  
% 2.92/1.42  
% 2.92/1.42  %Foreground operators:
% 2.92/1.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.92/1.42  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.92/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.92/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.92/1.42  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.92/1.42  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.92/1.42  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.92/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.92/1.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.92/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.92/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.92/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.92/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.92/1.42  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.92/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.92/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.92/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.92/1.42  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 2.92/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.92/1.42  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.92/1.42  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.92/1.42  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.92/1.42  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 2.92/1.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.92/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.92/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.92/1.42  
% 2.92/1.44  tff(f_164, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_tmap_1)).
% 2.92/1.44  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.92/1.44  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 2.92/1.44  tff(f_82, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 2.92/1.44  tff(f_104, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 2.92/1.44  tff(f_73, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.92/1.44  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.92/1.44  tff(f_47, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 2.92/1.44  tff(f_57, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_funct_2)).
% 2.92/1.44  tff(f_39, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.92/1.44  tff(f_131, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 2.92/1.44  tff(c_54, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.92/1.44  tff(c_18, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.92/1.44  tff(c_58, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.92/1.44  tff(c_42, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.92/1.44  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.92/1.44  tff(c_20, plain, (![A_16]: (m1_subset_1(u1_pre_topc(A_16), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_16)))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.92/1.44  tff(c_36, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.92/1.44  tff(c_83, plain, (![D_65, B_66, C_67, A_68]: (D_65=B_66 | g1_pre_topc(C_67, D_65)!=g1_pre_topc(A_68, B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(k1_zfmisc_1(A_68))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.92/1.44  tff(c_87, plain, (![D_65, C_67]: (u1_pre_topc('#skF_2')=D_65 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(C_67, D_65) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_36, c_83])).
% 2.92/1.44  tff(c_133, plain, (~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_87])).
% 2.92/1.44  tff(c_136, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_133])).
% 2.92/1.44  tff(c_140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_136])).
% 2.92/1.44  tff(c_141, plain, (![D_65, C_67]: (u1_pre_topc('#skF_2')=D_65 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(C_67, D_65))), inference(splitRight, [status(thm)], [c_87])).
% 2.92/1.44  tff(c_159, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_141])).
% 2.92/1.44  tff(c_142, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_87])).
% 2.92/1.44  tff(c_174, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_142])).
% 2.92/1.44  tff(c_175, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_3'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_36])).
% 2.92/1.44  tff(c_26, plain, (![C_22, A_18, D_23, B_19]: (C_22=A_18 | g1_pre_topc(C_22, D_23)!=g1_pre_topc(A_18, B_19) | ~m1_subset_1(B_19, k1_zfmisc_1(k1_zfmisc_1(A_18))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.92/1.44  tff(c_195, plain, (![C_22, D_23]: (u1_struct_0('#skF_2')=C_22 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(C_22, D_23) | ~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_175, c_26])).
% 2.92/1.44  tff(c_203, plain, (![C_22, D_23]: (u1_struct_0('#skF_2')=C_22 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(C_22, D_23))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_195])).
% 2.92/1.44  tff(c_218, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_203])).
% 2.92/1.44  tff(c_40, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.92/1.44  tff(c_232, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_218, c_40])).
% 2.92/1.44  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.92/1.44  tff(c_231, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_218, c_38])).
% 2.92/1.44  tff(c_282, plain, (![C_102, B_103, A_105, F_104, D_106]: (r1_funct_2(A_105, B_103, C_102, D_106, F_104, F_104) | ~m1_subset_1(F_104, k1_zfmisc_1(k2_zfmisc_1(C_102, D_106))) | ~v1_funct_2(F_104, C_102, D_106) | ~m1_subset_1(F_104, k1_zfmisc_1(k2_zfmisc_1(A_105, B_103))) | ~v1_funct_2(F_104, A_105, B_103) | ~v1_funct_1(F_104) | v1_xboole_0(D_106) | v1_xboole_0(B_103))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.92/1.44  tff(c_284, plain, (![A_105, B_103]: (r1_funct_2(A_105, B_103, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_105, B_103))) | ~v1_funct_2('#skF_4', A_105, B_103) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_103))), inference(resolution, [status(thm)], [c_231, c_282])).
% 2.92/1.44  tff(c_289, plain, (![A_105, B_103]: (r1_funct_2(A_105, B_103, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_105, B_103))) | ~v1_funct_2('#skF_4', A_105, B_103) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_103))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_232, c_284])).
% 2.92/1.44  tff(c_322, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_289])).
% 2.92/1.44  tff(c_22, plain, (![A_17]: (~v1_xboole_0(u1_struct_0(A_17)) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.92/1.44  tff(c_325, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_322, c_22])).
% 2.92/1.44  tff(c_328, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_58, c_325])).
% 2.92/1.44  tff(c_331, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_328])).
% 2.92/1.44  tff(c_335, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_331])).
% 2.92/1.44  tff(c_337, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_289])).
% 2.92/1.44  tff(c_336, plain, (![A_105, B_103]: (r1_funct_2(A_105, B_103, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_105, B_103))) | ~v1_funct_2('#skF_4', A_105, B_103) | v1_xboole_0(B_103))), inference(splitRight, [status(thm)], [c_289])).
% 2.92/1.44  tff(c_44, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.92/1.44  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.92/1.44  tff(c_12, plain, (![A_7, B_8, C_9, D_10]: (m1_subset_1(k2_partfun1(A_7, B_8, C_9, D_10), k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))) | ~v1_funct_1(C_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.92/1.44  tff(c_16, plain, (![A_11, B_12, D_14, C_13]: (r2_relset_1(A_11, B_12, k2_partfun1(A_11, B_12, D_14, C_13), D_14) | ~r1_tarski(A_11, C_13) | ~m1_subset_1(D_14, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))) | ~v1_funct_2(D_14, A_11, B_12) | ~v1_funct_1(D_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.92/1.44  tff(c_261, plain, (![C_13]: (r2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', C_13), '#skF_4') | ~r1_tarski(u1_struct_0('#skF_3'), C_13) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_231, c_16])).
% 2.92/1.44  tff(c_298, plain, (![C_109]: (r2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', C_109), '#skF_4') | ~r1_tarski(u1_struct_0('#skF_3'), C_109))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_232, c_261])).
% 2.92/1.44  tff(c_10, plain, (![D_6, C_5, A_3, B_4]: (D_6=C_5 | ~r2_relset_1(A_3, B_4, C_5, D_6) | ~m1_subset_1(D_6, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))) | ~m1_subset_1(C_5, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.92/1.44  tff(c_300, plain, (![C_109]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', C_109)='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', C_109), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~r1_tarski(u1_struct_0('#skF_3'), C_109))), inference(resolution, [status(thm)], [c_298, c_10])).
% 2.92/1.44  tff(c_346, plain, (![C_129]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', C_129)='#skF_4' | ~m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', C_129), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~r1_tarski(u1_struct_0('#skF_3'), C_129))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_300])).
% 2.92/1.44  tff(c_350, plain, (![D_10]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', D_10)='#skF_4' | ~r1_tarski(u1_struct_0('#skF_3'), D_10) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_12, c_346])).
% 2.92/1.44  tff(c_353, plain, (![D_10]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', D_10)='#skF_4' | ~r1_tarski(u1_struct_0('#skF_3'), D_10))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_231, c_350])).
% 2.92/1.44  tff(c_56, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.92/1.44  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.92/1.44  tff(c_50, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.92/1.44  tff(c_398, plain, (![A_132, B_133, C_134, D_135]: (k2_partfun1(u1_struct_0(A_132), u1_struct_0(B_133), C_134, u1_struct_0(D_135))=k2_tmap_1(A_132, B_133, C_134, D_135) | ~m1_pre_topc(D_135, A_132) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_132), u1_struct_0(B_133)))) | ~v1_funct_2(C_134, u1_struct_0(A_132), u1_struct_0(B_133)) | ~v1_funct_1(C_134) | ~l1_pre_topc(B_133) | ~v2_pre_topc(B_133) | v2_struct_0(B_133) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132) | v2_struct_0(A_132))), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.92/1.44  tff(c_402, plain, (![B_133, C_134, D_135]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_133), C_134, u1_struct_0(D_135))=k2_tmap_1('#skF_2', B_133, C_134, D_135) | ~m1_pre_topc(D_135, '#skF_2') | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_133)))) | ~v1_funct_2(C_134, u1_struct_0('#skF_2'), u1_struct_0(B_133)) | ~v1_funct_1(C_134) | ~l1_pre_topc(B_133) | ~v2_pre_topc(B_133) | v2_struct_0(B_133) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_218, c_398])).
% 2.92/1.44  tff(c_413, plain, (![B_133, C_134, D_135]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_133), C_134, u1_struct_0(D_135))=k2_tmap_1('#skF_2', B_133, C_134, D_135) | ~m1_pre_topc(D_135, '#skF_2') | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_133)))) | ~v1_funct_2(C_134, u1_struct_0('#skF_3'), u1_struct_0(B_133)) | ~v1_funct_1(C_134) | ~l1_pre_topc(B_133) | ~v2_pre_topc(B_133) | v2_struct_0(B_133) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_218, c_218, c_402])).
% 2.92/1.44  tff(c_425, plain, (![B_142, C_143, D_144]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_142), C_143, u1_struct_0(D_144))=k2_tmap_1('#skF_2', B_142, C_143, D_144) | ~m1_pre_topc(D_144, '#skF_2') | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_142)))) | ~v1_funct_2(C_143, u1_struct_0('#skF_3'), u1_struct_0(B_142)) | ~v1_funct_1(C_143) | ~l1_pre_topc(B_142) | ~v2_pre_topc(B_142) | v2_struct_0(B_142))), inference(negUnitSimplification, [status(thm)], [c_52, c_413])).
% 2.92/1.44  tff(c_427, plain, (![D_144]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_144))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_144) | ~m1_pre_topc(D_144, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_231, c_425])).
% 2.92/1.44  tff(c_435, plain, (![D_144]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_144))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_144) | ~m1_pre_topc(D_144, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_42, c_232, c_427])).
% 2.92/1.44  tff(c_441, plain, (![D_145]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_145))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_145) | ~m1_pre_topc(D_145, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_58, c_435])).
% 2.92/1.44  tff(c_495, plain, (![D_149]: (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_149)='#skF_4' | ~m1_pre_topc(D_149, '#skF_2') | ~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0(D_149)))), inference(superposition, [status(thm), theory('equality')], [c_353, c_441])).
% 2.92/1.44  tff(c_502, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_6, c_495])).
% 2.92/1.44  tff(c_507, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_502])).
% 2.92/1.44  tff(c_34, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.92/1.44  tff(c_229, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_218, c_34])).
% 2.92/1.44  tff(c_508, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_507, c_229])).
% 2.92/1.44  tff(c_545, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_336, c_508])).
% 2.92/1.44  tff(c_548, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_232, c_231, c_545])).
% 2.92/1.44  tff(c_550, plain, $false, inference(negUnitSimplification, [status(thm)], [c_337, c_548])).
% 2.92/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.44  
% 2.92/1.44  Inference rules
% 2.92/1.44  ----------------------
% 2.92/1.44  #Ref     : 7
% 2.92/1.44  #Sup     : 94
% 2.92/1.44  #Fact    : 0
% 2.92/1.44  #Define  : 0
% 2.92/1.44  #Split   : 5
% 2.92/1.44  #Chain   : 0
% 2.92/1.44  #Close   : 0
% 2.92/1.44  
% 2.92/1.44  Ordering : KBO
% 2.92/1.44  
% 2.92/1.44  Simplification rules
% 2.92/1.44  ----------------------
% 2.92/1.44  #Subsume      : 13
% 2.92/1.44  #Demod        : 115
% 2.92/1.44  #Tautology    : 42
% 2.92/1.44  #SimpNegUnit  : 9
% 2.92/1.44  #BackRed      : 11
% 2.92/1.44  
% 2.92/1.44  #Partial instantiations: 0
% 2.92/1.44  #Strategies tried      : 1
% 2.92/1.44  
% 2.92/1.44  Timing (in seconds)
% 2.92/1.44  ----------------------
% 2.92/1.44  Preprocessing        : 0.35
% 2.92/1.44  Parsing              : 0.19
% 2.92/1.45  CNF conversion       : 0.03
% 2.92/1.45  Main loop            : 0.33
% 2.92/1.45  Inferencing          : 0.12
% 2.92/1.45  Reduction            : 0.11
% 2.92/1.45  Demodulation         : 0.08
% 2.92/1.45  BG Simplification    : 0.02
% 2.92/1.45  Subsumption          : 0.06
% 2.92/1.45  Abstraction          : 0.02
% 2.92/1.45  MUC search           : 0.00
% 2.92/1.45  Cooper               : 0.00
% 2.92/1.45  Total                : 0.72
% 2.92/1.45  Index Insertion      : 0.00
% 2.92/1.45  Index Deletion       : 0.00
% 2.92/1.45  Index Matching       : 0.00
% 2.92/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
