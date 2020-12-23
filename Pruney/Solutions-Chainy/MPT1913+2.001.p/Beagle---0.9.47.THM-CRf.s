%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:43 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   61 (  94 expanded)
%              Number of leaves         :   26 (  48 expanded)
%              Depth                    :   15
%              Number of atoms          :  226 ( 446 expanded)
%              Number of equality atoms :   23 (  40 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_pralg_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k10_pralg_1 > k1_funct_1 > k12_pralg_1 > #nlpp > u1_struct_0 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k10_pralg_1,type,(
    k10_pralg_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k12_pralg_1,type,(
    k12_pralg_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pralg_1,type,(
    v2_pralg_1: $i > $o )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( v1_relat_1(B)
              & v4_relat_1(B,A)
              & v1_funct_1(B)
              & v1_partfun1(B,A)
              & v2_pralg_1(B) )
           => ! [C] :
                ( m1_subset_1(C,A)
               => k1_funct_1(k12_pralg_1(A,B),C) = u1_struct_0(k10_pralg_1(A,B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_6)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A)
        & v1_funct_1(B)
        & v1_partfun1(B,A)
        & v2_pralg_1(B) )
     => ( v1_relat_1(k12_pralg_1(A,B))
        & v4_relat_1(k12_pralg_1(A,B),A)
        & v1_funct_1(k12_pralg_1(A,B))
        & v1_partfun1(k12_pralg_1(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k12_pralg_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A)
        & v1_funct_1(B)
        & v1_partfun1(B,A)
        & v2_pralg_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A)
            & v1_funct_1(C)
            & v1_partfun1(C,A) )
         => ( C = k12_pralg_1(A,B)
          <=> ! [D] :
                ~ ( r2_hidden(D,A)
                  & ! [E] :
                      ( l1_struct_0(E)
                     => ~ ( E = k1_funct_1(B,D)
                          & k1_funct_1(C,D) = u1_struct_0(E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_pralg_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(B)
        & v4_relat_1(B,A)
        & v1_funct_1(B)
        & v1_partfun1(B,A)
        & v2_pralg_1(B)
        & m1_subset_1(C,A) )
     => k10_pralg_1(A,B,C) = k1_funct_1(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k10_pralg_1)).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_32,plain,(
    m1_subset_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r2_hidden(B_2,A_1)
      | ~ m1_subset_1(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_42,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_40,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_38,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_36,plain,(
    v1_partfun1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_34,plain,(
    v2_pralg_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_22,plain,(
    ! [A_29,B_30] :
      ( v1_funct_1(k12_pralg_1(A_29,B_30))
      | ~ v2_pralg_1(B_30)
      | ~ v1_partfun1(B_30,A_29)
      | ~ v1_funct_1(B_30)
      | ~ v4_relat_1(B_30,A_29)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_26,plain,(
    ! [A_29,B_30] :
      ( v1_relat_1(k12_pralg_1(A_29,B_30))
      | ~ v2_pralg_1(B_30)
      | ~ v1_partfun1(B_30,A_29)
      | ~ v1_funct_1(B_30)
      | ~ v4_relat_1(B_30,A_29)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_20,plain,(
    ! [A_29,B_30] :
      ( v1_partfun1(k12_pralg_1(A_29,B_30),A_29)
      | ~ v2_pralg_1(B_30)
      | ~ v1_partfun1(B_30,A_29)
      | ~ v1_funct_1(B_30)
      | ~ v4_relat_1(B_30,A_29)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_24,plain,(
    ! [A_29,B_30] :
      ( v4_relat_1(k12_pralg_1(A_29,B_30),A_29)
      | ~ v2_pralg_1(B_30)
      | ~ v1_partfun1(B_30,A_29)
      | ~ v1_funct_1(B_30)
      | ~ v4_relat_1(B_30,A_29)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_112,plain,(
    ! [A_69,B_70,D_71] :
      ( '#skF_1'(A_69,B_70,k12_pralg_1(A_69,B_70),D_71) = k1_funct_1(B_70,D_71)
      | ~ r2_hidden(D_71,A_69)
      | ~ v1_partfun1(k12_pralg_1(A_69,B_70),A_69)
      | ~ v1_funct_1(k12_pralg_1(A_69,B_70))
      | ~ v4_relat_1(k12_pralg_1(A_69,B_70),A_69)
      | ~ v1_relat_1(k12_pralg_1(A_69,B_70))
      | ~ v2_pralg_1(B_70)
      | ~ v1_partfun1(B_70,A_69)
      | ~ v1_funct_1(B_70)
      | ~ v4_relat_1(B_70,A_69)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_116,plain,(
    ! [A_72,B_73,D_74] :
      ( '#skF_1'(A_72,B_73,k12_pralg_1(A_72,B_73),D_74) = k1_funct_1(B_73,D_74)
      | ~ r2_hidden(D_74,A_72)
      | ~ v1_partfun1(k12_pralg_1(A_72,B_73),A_72)
      | ~ v1_funct_1(k12_pralg_1(A_72,B_73))
      | ~ v1_relat_1(k12_pralg_1(A_72,B_73))
      | ~ v2_pralg_1(B_73)
      | ~ v1_partfun1(B_73,A_72)
      | ~ v1_funct_1(B_73)
      | ~ v4_relat_1(B_73,A_72)
      | ~ v1_relat_1(B_73) ) ),
    inference(resolution,[status(thm)],[c_24,c_112])).

tff(c_120,plain,(
    ! [A_75,B_76,D_77] :
      ( '#skF_1'(A_75,B_76,k12_pralg_1(A_75,B_76),D_77) = k1_funct_1(B_76,D_77)
      | ~ r2_hidden(D_77,A_75)
      | ~ v1_funct_1(k12_pralg_1(A_75,B_76))
      | ~ v1_relat_1(k12_pralg_1(A_75,B_76))
      | ~ v2_pralg_1(B_76)
      | ~ v1_partfun1(B_76,A_75)
      | ~ v1_funct_1(B_76)
      | ~ v4_relat_1(B_76,A_75)
      | ~ v1_relat_1(B_76) ) ),
    inference(resolution,[status(thm)],[c_20,c_116])).

tff(c_124,plain,(
    ! [A_78,B_79,D_80] :
      ( '#skF_1'(A_78,B_79,k12_pralg_1(A_78,B_79),D_80) = k1_funct_1(B_79,D_80)
      | ~ r2_hidden(D_80,A_78)
      | ~ v1_funct_1(k12_pralg_1(A_78,B_79))
      | ~ v2_pralg_1(B_79)
      | ~ v1_partfun1(B_79,A_78)
      | ~ v1_funct_1(B_79)
      | ~ v4_relat_1(B_79,A_78)
      | ~ v1_relat_1(B_79) ) ),
    inference(resolution,[status(thm)],[c_26,c_120])).

tff(c_127,plain,(
    ! [A_29,B_30,D_80] :
      ( '#skF_1'(A_29,B_30,k12_pralg_1(A_29,B_30),D_80) = k1_funct_1(B_30,D_80)
      | ~ r2_hidden(D_80,A_29)
      | ~ v2_pralg_1(B_30)
      | ~ v1_partfun1(B_30,A_29)
      | ~ v1_funct_1(B_30)
      | ~ v4_relat_1(B_30,A_29)
      | ~ v1_relat_1(B_30) ) ),
    inference(resolution,[status(thm)],[c_22,c_124])).

tff(c_141,plain,(
    ! [A_87,B_88,D_89] :
      ( u1_struct_0('#skF_1'(A_87,B_88,k12_pralg_1(A_87,B_88),D_89)) = k1_funct_1(k12_pralg_1(A_87,B_88),D_89)
      | ~ r2_hidden(D_89,A_87)
      | ~ v1_partfun1(k12_pralg_1(A_87,B_88),A_87)
      | ~ v1_funct_1(k12_pralg_1(A_87,B_88))
      | ~ v4_relat_1(k12_pralg_1(A_87,B_88),A_87)
      | ~ v1_relat_1(k12_pralg_1(A_87,B_88))
      | ~ v2_pralg_1(B_88)
      | ~ v1_partfun1(B_88,A_87)
      | ~ v1_funct_1(B_88)
      | ~ v4_relat_1(B_88,A_87)
      | ~ v1_relat_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_208,plain,(
    ! [A_122,B_123,D_124] :
      ( k1_funct_1(k12_pralg_1(A_122,B_123),D_124) = u1_struct_0(k1_funct_1(B_123,D_124))
      | ~ r2_hidden(D_124,A_122)
      | ~ v1_partfun1(k12_pralg_1(A_122,B_123),A_122)
      | ~ v1_funct_1(k12_pralg_1(A_122,B_123))
      | ~ v4_relat_1(k12_pralg_1(A_122,B_123),A_122)
      | ~ v1_relat_1(k12_pralg_1(A_122,B_123))
      | ~ v2_pralg_1(B_123)
      | ~ v1_partfun1(B_123,A_122)
      | ~ v1_funct_1(B_123)
      | ~ v4_relat_1(B_123,A_122)
      | ~ v1_relat_1(B_123)
      | ~ r2_hidden(D_124,A_122)
      | ~ v2_pralg_1(B_123)
      | ~ v1_partfun1(B_123,A_122)
      | ~ v1_funct_1(B_123)
      | ~ v4_relat_1(B_123,A_122)
      | ~ v1_relat_1(B_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_141])).

tff(c_212,plain,(
    ! [A_125,B_126,D_127] :
      ( k1_funct_1(k12_pralg_1(A_125,B_126),D_127) = u1_struct_0(k1_funct_1(B_126,D_127))
      | ~ v1_partfun1(k12_pralg_1(A_125,B_126),A_125)
      | ~ v1_funct_1(k12_pralg_1(A_125,B_126))
      | ~ v1_relat_1(k12_pralg_1(A_125,B_126))
      | ~ r2_hidden(D_127,A_125)
      | ~ v2_pralg_1(B_126)
      | ~ v1_partfun1(B_126,A_125)
      | ~ v1_funct_1(B_126)
      | ~ v4_relat_1(B_126,A_125)
      | ~ v1_relat_1(B_126) ) ),
    inference(resolution,[status(thm)],[c_24,c_208])).

tff(c_216,plain,(
    ! [A_128,B_129,D_130] :
      ( k1_funct_1(k12_pralg_1(A_128,B_129),D_130) = u1_struct_0(k1_funct_1(B_129,D_130))
      | ~ v1_funct_1(k12_pralg_1(A_128,B_129))
      | ~ v1_relat_1(k12_pralg_1(A_128,B_129))
      | ~ r2_hidden(D_130,A_128)
      | ~ v2_pralg_1(B_129)
      | ~ v1_partfun1(B_129,A_128)
      | ~ v1_funct_1(B_129)
      | ~ v4_relat_1(B_129,A_128)
      | ~ v1_relat_1(B_129) ) ),
    inference(resolution,[status(thm)],[c_20,c_212])).

tff(c_220,plain,(
    ! [A_131,B_132,D_133] :
      ( k1_funct_1(k12_pralg_1(A_131,B_132),D_133) = u1_struct_0(k1_funct_1(B_132,D_133))
      | ~ v1_funct_1(k12_pralg_1(A_131,B_132))
      | ~ r2_hidden(D_133,A_131)
      | ~ v2_pralg_1(B_132)
      | ~ v1_partfun1(B_132,A_131)
      | ~ v1_funct_1(B_132)
      | ~ v4_relat_1(B_132,A_131)
      | ~ v1_relat_1(B_132) ) ),
    inference(resolution,[status(thm)],[c_26,c_216])).

tff(c_224,plain,(
    ! [A_134,B_135,D_136] :
      ( k1_funct_1(k12_pralg_1(A_134,B_135),D_136) = u1_struct_0(k1_funct_1(B_135,D_136))
      | ~ r2_hidden(D_136,A_134)
      | ~ v2_pralg_1(B_135)
      | ~ v1_partfun1(B_135,A_134)
      | ~ v1_funct_1(B_135)
      | ~ v4_relat_1(B_135,A_134)
      | ~ v1_relat_1(B_135) ) ),
    inference(resolution,[status(thm)],[c_22,c_220])).

tff(c_65,plain,(
    ! [A_54,B_55,C_56] :
      ( k10_pralg_1(A_54,B_55,C_56) = k1_funct_1(B_55,C_56)
      | ~ m1_subset_1(C_56,A_54)
      | ~ v2_pralg_1(B_55)
      | ~ v1_partfun1(B_55,A_54)
      | ~ v1_funct_1(B_55)
      | ~ v4_relat_1(B_55,A_54)
      | ~ v1_relat_1(B_55)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_69,plain,(
    ! [B_55] :
      ( k10_pralg_1('#skF_3',B_55,'#skF_5') = k1_funct_1(B_55,'#skF_5')
      | ~ v2_pralg_1(B_55)
      | ~ v1_partfun1(B_55,'#skF_3')
      | ~ v1_funct_1(B_55)
      | ~ v4_relat_1(B_55,'#skF_3')
      | ~ v1_relat_1(B_55)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_65])).

tff(c_74,plain,(
    ! [B_57] :
      ( k10_pralg_1('#skF_3',B_57,'#skF_5') = k1_funct_1(B_57,'#skF_5')
      | ~ v2_pralg_1(B_57)
      | ~ v1_partfun1(B_57,'#skF_3')
      | ~ v1_funct_1(B_57)
      | ~ v4_relat_1(B_57,'#skF_3')
      | ~ v1_relat_1(B_57) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_69])).

tff(c_81,plain,
    ( k10_pralg_1('#skF_3','#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_5')
    | ~ v2_pralg_1('#skF_4')
    | ~ v1_partfun1('#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_74])).

tff(c_85,plain,(
    k10_pralg_1('#skF_3','#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_36,c_34,c_81])).

tff(c_30,plain,(
    k1_funct_1(k12_pralg_1('#skF_3','#skF_4'),'#skF_5') != u1_struct_0(k10_pralg_1('#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_86,plain,(
    k1_funct_1(k12_pralg_1('#skF_3','#skF_4'),'#skF_5') != u1_struct_0(k1_funct_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_30])).

tff(c_239,plain,
    ( ~ r2_hidden('#skF_5','#skF_3')
    | ~ v2_pralg_1('#skF_4')
    | ~ v1_partfun1('#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_86])).

tff(c_246,plain,(
    ~ r2_hidden('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_34,c_239])).

tff(c_250,plain,
    ( ~ m1_subset_1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_246])).

tff(c_253,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_250])).

tff(c_255,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_253])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:05:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.44  
% 2.67/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.44  %$ v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_pralg_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k10_pralg_1 > k1_funct_1 > k12_pralg_1 > #nlpp > u1_struct_0 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 2.67/1.44  
% 2.67/1.44  %Foreground sorts:
% 2.67/1.44  
% 2.67/1.44  
% 2.67/1.44  %Background operators:
% 2.67/1.44  
% 2.67/1.44  
% 2.67/1.44  %Foreground operators:
% 2.67/1.44  tff(k10_pralg_1, type, k10_pralg_1: ($i * $i * $i) > $i).
% 2.67/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.67/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.44  tff(k12_pralg_1, type, k12_pralg_1: ($i * $i) > $i).
% 2.67/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.67/1.44  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.67/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.67/1.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.67/1.44  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.67/1.44  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.67/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.67/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.67/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.44  tff(v2_pralg_1, type, v2_pralg_1: $i > $o).
% 2.67/1.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.67/1.44  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.67/1.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.67/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.67/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.67/1.44  
% 2.67/1.45  tff(f_126, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((((v1_relat_1(B) & v4_relat_1(B, A)) & v1_funct_1(B)) & v1_partfun1(B, A)) & v2_pralg_1(B)) => (![C]: (m1_subset_1(C, A) => (k1_funct_1(k12_pralg_1(A, B), C) = u1_struct_0(k10_pralg_1(A, B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_yellow_6)).
% 2.67/1.45  tff(f_38, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.67/1.45  tff(f_89, axiom, (![A, B]: (((((v1_relat_1(B) & v4_relat_1(B, A)) & v1_funct_1(B)) & v1_partfun1(B, A)) & v2_pralg_1(B)) => (((v1_relat_1(k12_pralg_1(A, B)) & v4_relat_1(k12_pralg_1(A, B), A)) & v1_funct_1(k12_pralg_1(A, B))) & v1_partfun1(k12_pralg_1(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k12_pralg_1)).
% 2.67/1.45  tff(f_71, axiom, (![A, B]: (((((v1_relat_1(B) & v4_relat_1(B, A)) & v1_funct_1(B)) & v1_partfun1(B, A)) & v2_pralg_1(B)) => (![C]: ((((v1_relat_1(C) & v4_relat_1(C, A)) & v1_funct_1(C)) & v1_partfun1(C, A)) => ((C = k12_pralg_1(A, B)) <=> (![D]: ~(r2_hidden(D, A) & (![E]: (l1_struct_0(E) => ~((E = k1_funct_1(B, D)) & (k1_funct_1(C, D) = u1_struct_0(E)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_pralg_1)).
% 2.67/1.45  tff(f_106, axiom, (![A, B, C]: (((((((~v1_xboole_0(A) & v1_relat_1(B)) & v4_relat_1(B, A)) & v1_funct_1(B)) & v1_partfun1(B, A)) & v2_pralg_1(B)) & m1_subset_1(C, A)) => (k10_pralg_1(A, B, C) = k1_funct_1(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k10_pralg_1)).
% 2.67/1.45  tff(c_44, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.67/1.45  tff(c_32, plain, (m1_subset_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.67/1.45  tff(c_4, plain, (![B_2, A_1]: (r2_hidden(B_2, A_1) | ~m1_subset_1(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.67/1.45  tff(c_42, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.67/1.45  tff(c_40, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.67/1.45  tff(c_38, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.67/1.45  tff(c_36, plain, (v1_partfun1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.67/1.45  tff(c_34, plain, (v2_pralg_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.67/1.45  tff(c_22, plain, (![A_29, B_30]: (v1_funct_1(k12_pralg_1(A_29, B_30)) | ~v2_pralg_1(B_30) | ~v1_partfun1(B_30, A_29) | ~v1_funct_1(B_30) | ~v4_relat_1(B_30, A_29) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.67/1.45  tff(c_26, plain, (![A_29, B_30]: (v1_relat_1(k12_pralg_1(A_29, B_30)) | ~v2_pralg_1(B_30) | ~v1_partfun1(B_30, A_29) | ~v1_funct_1(B_30) | ~v4_relat_1(B_30, A_29) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.67/1.45  tff(c_20, plain, (![A_29, B_30]: (v1_partfun1(k12_pralg_1(A_29, B_30), A_29) | ~v2_pralg_1(B_30) | ~v1_partfun1(B_30, A_29) | ~v1_funct_1(B_30) | ~v4_relat_1(B_30, A_29) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.67/1.45  tff(c_24, plain, (![A_29, B_30]: (v4_relat_1(k12_pralg_1(A_29, B_30), A_29) | ~v2_pralg_1(B_30) | ~v1_partfun1(B_30, A_29) | ~v1_funct_1(B_30) | ~v4_relat_1(B_30, A_29) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.67/1.45  tff(c_112, plain, (![A_69, B_70, D_71]: ('#skF_1'(A_69, B_70, k12_pralg_1(A_69, B_70), D_71)=k1_funct_1(B_70, D_71) | ~r2_hidden(D_71, A_69) | ~v1_partfun1(k12_pralg_1(A_69, B_70), A_69) | ~v1_funct_1(k12_pralg_1(A_69, B_70)) | ~v4_relat_1(k12_pralg_1(A_69, B_70), A_69) | ~v1_relat_1(k12_pralg_1(A_69, B_70)) | ~v2_pralg_1(B_70) | ~v1_partfun1(B_70, A_69) | ~v1_funct_1(B_70) | ~v4_relat_1(B_70, A_69) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.67/1.45  tff(c_116, plain, (![A_72, B_73, D_74]: ('#skF_1'(A_72, B_73, k12_pralg_1(A_72, B_73), D_74)=k1_funct_1(B_73, D_74) | ~r2_hidden(D_74, A_72) | ~v1_partfun1(k12_pralg_1(A_72, B_73), A_72) | ~v1_funct_1(k12_pralg_1(A_72, B_73)) | ~v1_relat_1(k12_pralg_1(A_72, B_73)) | ~v2_pralg_1(B_73) | ~v1_partfun1(B_73, A_72) | ~v1_funct_1(B_73) | ~v4_relat_1(B_73, A_72) | ~v1_relat_1(B_73))), inference(resolution, [status(thm)], [c_24, c_112])).
% 2.67/1.45  tff(c_120, plain, (![A_75, B_76, D_77]: ('#skF_1'(A_75, B_76, k12_pralg_1(A_75, B_76), D_77)=k1_funct_1(B_76, D_77) | ~r2_hidden(D_77, A_75) | ~v1_funct_1(k12_pralg_1(A_75, B_76)) | ~v1_relat_1(k12_pralg_1(A_75, B_76)) | ~v2_pralg_1(B_76) | ~v1_partfun1(B_76, A_75) | ~v1_funct_1(B_76) | ~v4_relat_1(B_76, A_75) | ~v1_relat_1(B_76))), inference(resolution, [status(thm)], [c_20, c_116])).
% 2.67/1.45  tff(c_124, plain, (![A_78, B_79, D_80]: ('#skF_1'(A_78, B_79, k12_pralg_1(A_78, B_79), D_80)=k1_funct_1(B_79, D_80) | ~r2_hidden(D_80, A_78) | ~v1_funct_1(k12_pralg_1(A_78, B_79)) | ~v2_pralg_1(B_79) | ~v1_partfun1(B_79, A_78) | ~v1_funct_1(B_79) | ~v4_relat_1(B_79, A_78) | ~v1_relat_1(B_79))), inference(resolution, [status(thm)], [c_26, c_120])).
% 2.67/1.45  tff(c_127, plain, (![A_29, B_30, D_80]: ('#skF_1'(A_29, B_30, k12_pralg_1(A_29, B_30), D_80)=k1_funct_1(B_30, D_80) | ~r2_hidden(D_80, A_29) | ~v2_pralg_1(B_30) | ~v1_partfun1(B_30, A_29) | ~v1_funct_1(B_30) | ~v4_relat_1(B_30, A_29) | ~v1_relat_1(B_30))), inference(resolution, [status(thm)], [c_22, c_124])).
% 2.67/1.45  tff(c_141, plain, (![A_87, B_88, D_89]: (u1_struct_0('#skF_1'(A_87, B_88, k12_pralg_1(A_87, B_88), D_89))=k1_funct_1(k12_pralg_1(A_87, B_88), D_89) | ~r2_hidden(D_89, A_87) | ~v1_partfun1(k12_pralg_1(A_87, B_88), A_87) | ~v1_funct_1(k12_pralg_1(A_87, B_88)) | ~v4_relat_1(k12_pralg_1(A_87, B_88), A_87) | ~v1_relat_1(k12_pralg_1(A_87, B_88)) | ~v2_pralg_1(B_88) | ~v1_partfun1(B_88, A_87) | ~v1_funct_1(B_88) | ~v4_relat_1(B_88, A_87) | ~v1_relat_1(B_88))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.67/1.45  tff(c_208, plain, (![A_122, B_123, D_124]: (k1_funct_1(k12_pralg_1(A_122, B_123), D_124)=u1_struct_0(k1_funct_1(B_123, D_124)) | ~r2_hidden(D_124, A_122) | ~v1_partfun1(k12_pralg_1(A_122, B_123), A_122) | ~v1_funct_1(k12_pralg_1(A_122, B_123)) | ~v4_relat_1(k12_pralg_1(A_122, B_123), A_122) | ~v1_relat_1(k12_pralg_1(A_122, B_123)) | ~v2_pralg_1(B_123) | ~v1_partfun1(B_123, A_122) | ~v1_funct_1(B_123) | ~v4_relat_1(B_123, A_122) | ~v1_relat_1(B_123) | ~r2_hidden(D_124, A_122) | ~v2_pralg_1(B_123) | ~v1_partfun1(B_123, A_122) | ~v1_funct_1(B_123) | ~v4_relat_1(B_123, A_122) | ~v1_relat_1(B_123))), inference(superposition, [status(thm), theory('equality')], [c_127, c_141])).
% 2.67/1.45  tff(c_212, plain, (![A_125, B_126, D_127]: (k1_funct_1(k12_pralg_1(A_125, B_126), D_127)=u1_struct_0(k1_funct_1(B_126, D_127)) | ~v1_partfun1(k12_pralg_1(A_125, B_126), A_125) | ~v1_funct_1(k12_pralg_1(A_125, B_126)) | ~v1_relat_1(k12_pralg_1(A_125, B_126)) | ~r2_hidden(D_127, A_125) | ~v2_pralg_1(B_126) | ~v1_partfun1(B_126, A_125) | ~v1_funct_1(B_126) | ~v4_relat_1(B_126, A_125) | ~v1_relat_1(B_126))), inference(resolution, [status(thm)], [c_24, c_208])).
% 2.67/1.45  tff(c_216, plain, (![A_128, B_129, D_130]: (k1_funct_1(k12_pralg_1(A_128, B_129), D_130)=u1_struct_0(k1_funct_1(B_129, D_130)) | ~v1_funct_1(k12_pralg_1(A_128, B_129)) | ~v1_relat_1(k12_pralg_1(A_128, B_129)) | ~r2_hidden(D_130, A_128) | ~v2_pralg_1(B_129) | ~v1_partfun1(B_129, A_128) | ~v1_funct_1(B_129) | ~v4_relat_1(B_129, A_128) | ~v1_relat_1(B_129))), inference(resolution, [status(thm)], [c_20, c_212])).
% 2.67/1.45  tff(c_220, plain, (![A_131, B_132, D_133]: (k1_funct_1(k12_pralg_1(A_131, B_132), D_133)=u1_struct_0(k1_funct_1(B_132, D_133)) | ~v1_funct_1(k12_pralg_1(A_131, B_132)) | ~r2_hidden(D_133, A_131) | ~v2_pralg_1(B_132) | ~v1_partfun1(B_132, A_131) | ~v1_funct_1(B_132) | ~v4_relat_1(B_132, A_131) | ~v1_relat_1(B_132))), inference(resolution, [status(thm)], [c_26, c_216])).
% 2.67/1.45  tff(c_224, plain, (![A_134, B_135, D_136]: (k1_funct_1(k12_pralg_1(A_134, B_135), D_136)=u1_struct_0(k1_funct_1(B_135, D_136)) | ~r2_hidden(D_136, A_134) | ~v2_pralg_1(B_135) | ~v1_partfun1(B_135, A_134) | ~v1_funct_1(B_135) | ~v4_relat_1(B_135, A_134) | ~v1_relat_1(B_135))), inference(resolution, [status(thm)], [c_22, c_220])).
% 2.67/1.45  tff(c_65, plain, (![A_54, B_55, C_56]: (k10_pralg_1(A_54, B_55, C_56)=k1_funct_1(B_55, C_56) | ~m1_subset_1(C_56, A_54) | ~v2_pralg_1(B_55) | ~v1_partfun1(B_55, A_54) | ~v1_funct_1(B_55) | ~v4_relat_1(B_55, A_54) | ~v1_relat_1(B_55) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.67/1.45  tff(c_69, plain, (![B_55]: (k10_pralg_1('#skF_3', B_55, '#skF_5')=k1_funct_1(B_55, '#skF_5') | ~v2_pralg_1(B_55) | ~v1_partfun1(B_55, '#skF_3') | ~v1_funct_1(B_55) | ~v4_relat_1(B_55, '#skF_3') | ~v1_relat_1(B_55) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_65])).
% 2.67/1.45  tff(c_74, plain, (![B_57]: (k10_pralg_1('#skF_3', B_57, '#skF_5')=k1_funct_1(B_57, '#skF_5') | ~v2_pralg_1(B_57) | ~v1_partfun1(B_57, '#skF_3') | ~v1_funct_1(B_57) | ~v4_relat_1(B_57, '#skF_3') | ~v1_relat_1(B_57))), inference(negUnitSimplification, [status(thm)], [c_44, c_69])).
% 2.67/1.45  tff(c_81, plain, (k10_pralg_1('#skF_3', '#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_5') | ~v2_pralg_1('#skF_4') | ~v1_partfun1('#skF_4', '#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_74])).
% 2.67/1.45  tff(c_85, plain, (k10_pralg_1('#skF_3', '#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_36, c_34, c_81])).
% 2.67/1.45  tff(c_30, plain, (k1_funct_1(k12_pralg_1('#skF_3', '#skF_4'), '#skF_5')!=u1_struct_0(k10_pralg_1('#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.67/1.45  tff(c_86, plain, (k1_funct_1(k12_pralg_1('#skF_3', '#skF_4'), '#skF_5')!=u1_struct_0(k1_funct_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_30])).
% 2.67/1.45  tff(c_239, plain, (~r2_hidden('#skF_5', '#skF_3') | ~v2_pralg_1('#skF_4') | ~v1_partfun1('#skF_4', '#skF_3') | ~v1_funct_1('#skF_4') | ~v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_224, c_86])).
% 2.67/1.45  tff(c_246, plain, (~r2_hidden('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_34, c_239])).
% 2.67/1.45  tff(c_250, plain, (~m1_subset_1('#skF_5', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_4, c_246])).
% 2.67/1.45  tff(c_253, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_250])).
% 2.67/1.45  tff(c_255, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_253])).
% 2.67/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.45  
% 2.67/1.45  Inference rules
% 2.67/1.45  ----------------------
% 2.67/1.45  #Ref     : 0
% 2.67/1.45  #Sup     : 47
% 2.67/1.46  #Fact    : 0
% 2.67/1.46  #Define  : 0
% 2.67/1.46  #Split   : 0
% 2.67/1.46  #Chain   : 0
% 2.67/1.46  #Close   : 0
% 2.67/1.46  
% 2.67/1.46  Ordering : KBO
% 2.67/1.46  
% 2.67/1.46  Simplification rules
% 2.67/1.46  ----------------------
% 2.67/1.46  #Subsume      : 17
% 2.67/1.46  #Demod        : 15
% 2.67/1.46  #Tautology    : 14
% 2.67/1.46  #SimpNegUnit  : 3
% 2.67/1.46  #BackRed      : 1
% 2.67/1.46  
% 2.67/1.46  #Partial instantiations: 0
% 2.67/1.46  #Strategies tried      : 1
% 2.67/1.46  
% 2.67/1.46  Timing (in seconds)
% 2.67/1.46  ----------------------
% 2.67/1.46  Preprocessing        : 0.35
% 2.67/1.46  Parsing              : 0.18
% 2.67/1.46  CNF conversion       : 0.03
% 2.67/1.46  Main loop            : 0.28
% 2.67/1.46  Inferencing          : 0.11
% 2.67/1.46  Reduction            : 0.07
% 2.67/1.46  Demodulation         : 0.04
% 2.67/1.46  BG Simplification    : 0.02
% 2.67/1.46  Subsumption          : 0.07
% 2.67/1.46  Abstraction          : 0.01
% 2.67/1.46  MUC search           : 0.00
% 2.67/1.46  Cooper               : 0.00
% 2.67/1.46  Total                : 0.66
% 2.67/1.46  Index Insertion      : 0.00
% 2.67/1.46  Index Deletion       : 0.00
% 2.67/1.46  Index Matching       : 0.00
% 2.67/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
