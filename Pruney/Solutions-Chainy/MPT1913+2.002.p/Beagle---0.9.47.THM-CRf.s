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
% DateTime   : Thu Dec  3 10:30:43 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   61 (  94 expanded)
%              Number of leaves         :   26 (  48 expanded)
%              Depth                    :   15
%              Number of atoms          :  223 ( 443 expanded)
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

tff(f_119,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_82,axiom,(
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

tff(f_64,axiom,(
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

tff(f_99,axiom,(
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

tff(c_38,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_26,plain,(
    m1_subset_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_34,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_32,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_30,plain,(
    v1_partfun1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_28,plain,(
    v2_pralg_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_16,plain,(
    ! [A_29,B_30] :
      ( v1_funct_1(k12_pralg_1(A_29,B_30))
      | ~ v2_pralg_1(B_30)
      | ~ v1_partfun1(B_30,A_29)
      | ~ v1_funct_1(B_30)
      | ~ v4_relat_1(B_30,A_29)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_20,plain,(
    ! [A_29,B_30] :
      ( v1_relat_1(k12_pralg_1(A_29,B_30))
      | ~ v2_pralg_1(B_30)
      | ~ v1_partfun1(B_30,A_29)
      | ~ v1_funct_1(B_30)
      | ~ v4_relat_1(B_30,A_29)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_14,plain,(
    ! [A_29,B_30] :
      ( v1_partfun1(k12_pralg_1(A_29,B_30),A_29)
      | ~ v2_pralg_1(B_30)
      | ~ v1_partfun1(B_30,A_29)
      | ~ v1_funct_1(B_30)
      | ~ v4_relat_1(B_30,A_29)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_18,plain,(
    ! [A_29,B_30] :
      ( v4_relat_1(k12_pralg_1(A_29,B_30),A_29)
      | ~ v2_pralg_1(B_30)
      | ~ v1_partfun1(B_30,A_29)
      | ~ v1_funct_1(B_30)
      | ~ v4_relat_1(B_30,A_29)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_76,plain,(
    ! [A_60,B_61,D_62] :
      ( '#skF_1'(A_60,B_61,k12_pralg_1(A_60,B_61),D_62) = k1_funct_1(B_61,D_62)
      | ~ r2_hidden(D_62,A_60)
      | ~ v1_partfun1(k12_pralg_1(A_60,B_61),A_60)
      | ~ v1_funct_1(k12_pralg_1(A_60,B_61))
      | ~ v4_relat_1(k12_pralg_1(A_60,B_61),A_60)
      | ~ v1_relat_1(k12_pralg_1(A_60,B_61))
      | ~ v2_pralg_1(B_61)
      | ~ v1_partfun1(B_61,A_60)
      | ~ v1_funct_1(B_61)
      | ~ v4_relat_1(B_61,A_60)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_80,plain,(
    ! [A_63,B_64,D_65] :
      ( '#skF_1'(A_63,B_64,k12_pralg_1(A_63,B_64),D_65) = k1_funct_1(B_64,D_65)
      | ~ r2_hidden(D_65,A_63)
      | ~ v1_partfun1(k12_pralg_1(A_63,B_64),A_63)
      | ~ v1_funct_1(k12_pralg_1(A_63,B_64))
      | ~ v1_relat_1(k12_pralg_1(A_63,B_64))
      | ~ v2_pralg_1(B_64)
      | ~ v1_partfun1(B_64,A_63)
      | ~ v1_funct_1(B_64)
      | ~ v4_relat_1(B_64,A_63)
      | ~ v1_relat_1(B_64) ) ),
    inference(resolution,[status(thm)],[c_18,c_76])).

tff(c_84,plain,(
    ! [A_66,B_67,D_68] :
      ( '#skF_1'(A_66,B_67,k12_pralg_1(A_66,B_67),D_68) = k1_funct_1(B_67,D_68)
      | ~ r2_hidden(D_68,A_66)
      | ~ v1_funct_1(k12_pralg_1(A_66,B_67))
      | ~ v1_relat_1(k12_pralg_1(A_66,B_67))
      | ~ v2_pralg_1(B_67)
      | ~ v1_partfun1(B_67,A_66)
      | ~ v1_funct_1(B_67)
      | ~ v4_relat_1(B_67,A_66)
      | ~ v1_relat_1(B_67) ) ),
    inference(resolution,[status(thm)],[c_14,c_80])).

tff(c_88,plain,(
    ! [A_69,B_70,D_71] :
      ( '#skF_1'(A_69,B_70,k12_pralg_1(A_69,B_70),D_71) = k1_funct_1(B_70,D_71)
      | ~ r2_hidden(D_71,A_69)
      | ~ v1_funct_1(k12_pralg_1(A_69,B_70))
      | ~ v2_pralg_1(B_70)
      | ~ v1_partfun1(B_70,A_69)
      | ~ v1_funct_1(B_70)
      | ~ v4_relat_1(B_70,A_69)
      | ~ v1_relat_1(B_70) ) ),
    inference(resolution,[status(thm)],[c_20,c_84])).

tff(c_101,plain,(
    ! [A_75,B_76,D_77] :
      ( '#skF_1'(A_75,B_76,k12_pralg_1(A_75,B_76),D_77) = k1_funct_1(B_76,D_77)
      | ~ r2_hidden(D_77,A_75)
      | ~ v2_pralg_1(B_76)
      | ~ v1_partfun1(B_76,A_75)
      | ~ v1_funct_1(B_76)
      | ~ v4_relat_1(B_76,A_75)
      | ~ v1_relat_1(B_76) ) ),
    inference(resolution,[status(thm)],[c_16,c_88])).

tff(c_8,plain,(
    ! [A_3,B_4,D_25] :
      ( u1_struct_0('#skF_1'(A_3,B_4,k12_pralg_1(A_3,B_4),D_25)) = k1_funct_1(k12_pralg_1(A_3,B_4),D_25)
      | ~ r2_hidden(D_25,A_3)
      | ~ v1_partfun1(k12_pralg_1(A_3,B_4),A_3)
      | ~ v1_funct_1(k12_pralg_1(A_3,B_4))
      | ~ v4_relat_1(k12_pralg_1(A_3,B_4),A_3)
      | ~ v1_relat_1(k12_pralg_1(A_3,B_4))
      | ~ v2_pralg_1(B_4)
      | ~ v1_partfun1(B_4,A_3)
      | ~ v1_funct_1(B_4)
      | ~ v4_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_157,plain,(
    ! [A_102,B_103,D_104] :
      ( k1_funct_1(k12_pralg_1(A_102,B_103),D_104) = u1_struct_0(k1_funct_1(B_103,D_104))
      | ~ r2_hidden(D_104,A_102)
      | ~ v1_partfun1(k12_pralg_1(A_102,B_103),A_102)
      | ~ v1_funct_1(k12_pralg_1(A_102,B_103))
      | ~ v4_relat_1(k12_pralg_1(A_102,B_103),A_102)
      | ~ v1_relat_1(k12_pralg_1(A_102,B_103))
      | ~ v2_pralg_1(B_103)
      | ~ v1_partfun1(B_103,A_102)
      | ~ v1_funct_1(B_103)
      | ~ v4_relat_1(B_103,A_102)
      | ~ v1_relat_1(B_103)
      | ~ r2_hidden(D_104,A_102)
      | ~ v2_pralg_1(B_103)
      | ~ v1_partfun1(B_103,A_102)
      | ~ v1_funct_1(B_103)
      | ~ v4_relat_1(B_103,A_102)
      | ~ v1_relat_1(B_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_8])).

tff(c_162,plain,(
    ! [A_106,B_107,D_108] :
      ( k1_funct_1(k12_pralg_1(A_106,B_107),D_108) = u1_struct_0(k1_funct_1(B_107,D_108))
      | ~ v1_partfun1(k12_pralg_1(A_106,B_107),A_106)
      | ~ v1_funct_1(k12_pralg_1(A_106,B_107))
      | ~ v1_relat_1(k12_pralg_1(A_106,B_107))
      | ~ r2_hidden(D_108,A_106)
      | ~ v2_pralg_1(B_107)
      | ~ v1_partfun1(B_107,A_106)
      | ~ v1_funct_1(B_107)
      | ~ v4_relat_1(B_107,A_106)
      | ~ v1_relat_1(B_107) ) ),
    inference(resolution,[status(thm)],[c_18,c_157])).

tff(c_166,plain,(
    ! [A_109,B_110,D_111] :
      ( k1_funct_1(k12_pralg_1(A_109,B_110),D_111) = u1_struct_0(k1_funct_1(B_110,D_111))
      | ~ v1_funct_1(k12_pralg_1(A_109,B_110))
      | ~ v1_relat_1(k12_pralg_1(A_109,B_110))
      | ~ r2_hidden(D_111,A_109)
      | ~ v2_pralg_1(B_110)
      | ~ v1_partfun1(B_110,A_109)
      | ~ v1_funct_1(B_110)
      | ~ v4_relat_1(B_110,A_109)
      | ~ v1_relat_1(B_110) ) ),
    inference(resolution,[status(thm)],[c_14,c_162])).

tff(c_170,plain,(
    ! [A_112,B_113,D_114] :
      ( k1_funct_1(k12_pralg_1(A_112,B_113),D_114) = u1_struct_0(k1_funct_1(B_113,D_114))
      | ~ v1_funct_1(k12_pralg_1(A_112,B_113))
      | ~ r2_hidden(D_114,A_112)
      | ~ v2_pralg_1(B_113)
      | ~ v1_partfun1(B_113,A_112)
      | ~ v1_funct_1(B_113)
      | ~ v4_relat_1(B_113,A_112)
      | ~ v1_relat_1(B_113) ) ),
    inference(resolution,[status(thm)],[c_20,c_166])).

tff(c_174,plain,(
    ! [A_115,B_116,D_117] :
      ( k1_funct_1(k12_pralg_1(A_115,B_116),D_117) = u1_struct_0(k1_funct_1(B_116,D_117))
      | ~ r2_hidden(D_117,A_115)
      | ~ v2_pralg_1(B_116)
      | ~ v1_partfun1(B_116,A_115)
      | ~ v1_funct_1(B_116)
      | ~ v4_relat_1(B_116,A_115)
      | ~ v1_relat_1(B_116) ) ),
    inference(resolution,[status(thm)],[c_16,c_170])).

tff(c_44,plain,(
    ! [A_48,B_49,C_50] :
      ( k10_pralg_1(A_48,B_49,C_50) = k1_funct_1(B_49,C_50)
      | ~ m1_subset_1(C_50,A_48)
      | ~ v2_pralg_1(B_49)
      | ~ v1_partfun1(B_49,A_48)
      | ~ v1_funct_1(B_49)
      | ~ v4_relat_1(B_49,A_48)
      | ~ v1_relat_1(B_49)
      | v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_46,plain,(
    ! [B_49] :
      ( k10_pralg_1('#skF_3',B_49,'#skF_5') = k1_funct_1(B_49,'#skF_5')
      | ~ v2_pralg_1(B_49)
      | ~ v1_partfun1(B_49,'#skF_3')
      | ~ v1_funct_1(B_49)
      | ~ v4_relat_1(B_49,'#skF_3')
      | ~ v1_relat_1(B_49)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_44])).

tff(c_50,plain,(
    ! [B_51] :
      ( k10_pralg_1('#skF_3',B_51,'#skF_5') = k1_funct_1(B_51,'#skF_5')
      | ~ v2_pralg_1(B_51)
      | ~ v1_partfun1(B_51,'#skF_3')
      | ~ v1_funct_1(B_51)
      | ~ v4_relat_1(B_51,'#skF_3')
      | ~ v1_relat_1(B_51) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_46])).

tff(c_57,plain,
    ( k10_pralg_1('#skF_3','#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_5')
    | ~ v2_pralg_1('#skF_4')
    | ~ v1_partfun1('#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_50])).

tff(c_61,plain,(
    k10_pralg_1('#skF_3','#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_30,c_28,c_57])).

tff(c_24,plain,(
    k1_funct_1(k12_pralg_1('#skF_3','#skF_4'),'#skF_5') != u1_struct_0(k10_pralg_1('#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_63,plain,(
    k1_funct_1(k12_pralg_1('#skF_3','#skF_4'),'#skF_5') != u1_struct_0(k1_funct_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_24])).

tff(c_186,plain,
    ( ~ r2_hidden('#skF_5','#skF_3')
    | ~ v2_pralg_1('#skF_4')
    | ~ v1_partfun1('#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_63])).

tff(c_193,plain,(
    ~ r2_hidden('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_28,c_186])).

tff(c_197,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_193])).

tff(c_200,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_197])).

tff(c_202,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_200])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n008.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 16:16:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.42  
% 2.70/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.42  %$ v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_pralg_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k10_pralg_1 > k1_funct_1 > k12_pralg_1 > #nlpp > u1_struct_0 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 2.70/1.42  
% 2.70/1.42  %Foreground sorts:
% 2.70/1.42  
% 2.70/1.42  
% 2.70/1.42  %Background operators:
% 2.70/1.42  
% 2.70/1.42  
% 2.70/1.42  %Foreground operators:
% 2.70/1.42  tff(k10_pralg_1, type, k10_pralg_1: ($i * $i * $i) > $i).
% 2.70/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.70/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.70/1.42  tff(k12_pralg_1, type, k12_pralg_1: ($i * $i) > $i).
% 2.70/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.70/1.42  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.70/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.70/1.42  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.70/1.42  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.70/1.42  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.70/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.70/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.70/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.42  tff(v2_pralg_1, type, v2_pralg_1: $i > $o).
% 2.70/1.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.70/1.42  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.70/1.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.70/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.70/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.70/1.42  
% 2.70/1.44  tff(f_119, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((((v1_relat_1(B) & v4_relat_1(B, A)) & v1_funct_1(B)) & v1_partfun1(B, A)) & v2_pralg_1(B)) => (![C]: (m1_subset_1(C, A) => (k1_funct_1(k12_pralg_1(A, B), C) = u1_struct_0(k10_pralg_1(A, B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_yellow_6)).
% 2.70/1.44  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.70/1.44  tff(f_82, axiom, (![A, B]: (((((v1_relat_1(B) & v4_relat_1(B, A)) & v1_funct_1(B)) & v1_partfun1(B, A)) & v2_pralg_1(B)) => (((v1_relat_1(k12_pralg_1(A, B)) & v4_relat_1(k12_pralg_1(A, B), A)) & v1_funct_1(k12_pralg_1(A, B))) & v1_partfun1(k12_pralg_1(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k12_pralg_1)).
% 2.70/1.44  tff(f_64, axiom, (![A, B]: (((((v1_relat_1(B) & v4_relat_1(B, A)) & v1_funct_1(B)) & v1_partfun1(B, A)) & v2_pralg_1(B)) => (![C]: ((((v1_relat_1(C) & v4_relat_1(C, A)) & v1_funct_1(C)) & v1_partfun1(C, A)) => ((C = k12_pralg_1(A, B)) <=> (![D]: ~(r2_hidden(D, A) & (![E]: (l1_struct_0(E) => ~((E = k1_funct_1(B, D)) & (k1_funct_1(C, D) = u1_struct_0(E)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_pralg_1)).
% 2.70/1.44  tff(f_99, axiom, (![A, B, C]: (((((((~v1_xboole_0(A) & v1_relat_1(B)) & v4_relat_1(B, A)) & v1_funct_1(B)) & v1_partfun1(B, A)) & v2_pralg_1(B)) & m1_subset_1(C, A)) => (k10_pralg_1(A, B, C) = k1_funct_1(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k10_pralg_1)).
% 2.70/1.44  tff(c_38, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.70/1.44  tff(c_26, plain, (m1_subset_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.70/1.44  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.70/1.44  tff(c_36, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.70/1.44  tff(c_34, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.70/1.44  tff(c_32, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.70/1.44  tff(c_30, plain, (v1_partfun1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.70/1.44  tff(c_28, plain, (v2_pralg_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.70/1.44  tff(c_16, plain, (![A_29, B_30]: (v1_funct_1(k12_pralg_1(A_29, B_30)) | ~v2_pralg_1(B_30) | ~v1_partfun1(B_30, A_29) | ~v1_funct_1(B_30) | ~v4_relat_1(B_30, A_29) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.70/1.44  tff(c_20, plain, (![A_29, B_30]: (v1_relat_1(k12_pralg_1(A_29, B_30)) | ~v2_pralg_1(B_30) | ~v1_partfun1(B_30, A_29) | ~v1_funct_1(B_30) | ~v4_relat_1(B_30, A_29) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.70/1.44  tff(c_14, plain, (![A_29, B_30]: (v1_partfun1(k12_pralg_1(A_29, B_30), A_29) | ~v2_pralg_1(B_30) | ~v1_partfun1(B_30, A_29) | ~v1_funct_1(B_30) | ~v4_relat_1(B_30, A_29) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.70/1.44  tff(c_18, plain, (![A_29, B_30]: (v4_relat_1(k12_pralg_1(A_29, B_30), A_29) | ~v2_pralg_1(B_30) | ~v1_partfun1(B_30, A_29) | ~v1_funct_1(B_30) | ~v4_relat_1(B_30, A_29) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.70/1.44  tff(c_76, plain, (![A_60, B_61, D_62]: ('#skF_1'(A_60, B_61, k12_pralg_1(A_60, B_61), D_62)=k1_funct_1(B_61, D_62) | ~r2_hidden(D_62, A_60) | ~v1_partfun1(k12_pralg_1(A_60, B_61), A_60) | ~v1_funct_1(k12_pralg_1(A_60, B_61)) | ~v4_relat_1(k12_pralg_1(A_60, B_61), A_60) | ~v1_relat_1(k12_pralg_1(A_60, B_61)) | ~v2_pralg_1(B_61) | ~v1_partfun1(B_61, A_60) | ~v1_funct_1(B_61) | ~v4_relat_1(B_61, A_60) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.70/1.44  tff(c_80, plain, (![A_63, B_64, D_65]: ('#skF_1'(A_63, B_64, k12_pralg_1(A_63, B_64), D_65)=k1_funct_1(B_64, D_65) | ~r2_hidden(D_65, A_63) | ~v1_partfun1(k12_pralg_1(A_63, B_64), A_63) | ~v1_funct_1(k12_pralg_1(A_63, B_64)) | ~v1_relat_1(k12_pralg_1(A_63, B_64)) | ~v2_pralg_1(B_64) | ~v1_partfun1(B_64, A_63) | ~v1_funct_1(B_64) | ~v4_relat_1(B_64, A_63) | ~v1_relat_1(B_64))), inference(resolution, [status(thm)], [c_18, c_76])).
% 2.70/1.44  tff(c_84, plain, (![A_66, B_67, D_68]: ('#skF_1'(A_66, B_67, k12_pralg_1(A_66, B_67), D_68)=k1_funct_1(B_67, D_68) | ~r2_hidden(D_68, A_66) | ~v1_funct_1(k12_pralg_1(A_66, B_67)) | ~v1_relat_1(k12_pralg_1(A_66, B_67)) | ~v2_pralg_1(B_67) | ~v1_partfun1(B_67, A_66) | ~v1_funct_1(B_67) | ~v4_relat_1(B_67, A_66) | ~v1_relat_1(B_67))), inference(resolution, [status(thm)], [c_14, c_80])).
% 2.70/1.44  tff(c_88, plain, (![A_69, B_70, D_71]: ('#skF_1'(A_69, B_70, k12_pralg_1(A_69, B_70), D_71)=k1_funct_1(B_70, D_71) | ~r2_hidden(D_71, A_69) | ~v1_funct_1(k12_pralg_1(A_69, B_70)) | ~v2_pralg_1(B_70) | ~v1_partfun1(B_70, A_69) | ~v1_funct_1(B_70) | ~v4_relat_1(B_70, A_69) | ~v1_relat_1(B_70))), inference(resolution, [status(thm)], [c_20, c_84])).
% 2.70/1.44  tff(c_101, plain, (![A_75, B_76, D_77]: ('#skF_1'(A_75, B_76, k12_pralg_1(A_75, B_76), D_77)=k1_funct_1(B_76, D_77) | ~r2_hidden(D_77, A_75) | ~v2_pralg_1(B_76) | ~v1_partfun1(B_76, A_75) | ~v1_funct_1(B_76) | ~v4_relat_1(B_76, A_75) | ~v1_relat_1(B_76))), inference(resolution, [status(thm)], [c_16, c_88])).
% 2.70/1.44  tff(c_8, plain, (![A_3, B_4, D_25]: (u1_struct_0('#skF_1'(A_3, B_4, k12_pralg_1(A_3, B_4), D_25))=k1_funct_1(k12_pralg_1(A_3, B_4), D_25) | ~r2_hidden(D_25, A_3) | ~v1_partfun1(k12_pralg_1(A_3, B_4), A_3) | ~v1_funct_1(k12_pralg_1(A_3, B_4)) | ~v4_relat_1(k12_pralg_1(A_3, B_4), A_3) | ~v1_relat_1(k12_pralg_1(A_3, B_4)) | ~v2_pralg_1(B_4) | ~v1_partfun1(B_4, A_3) | ~v1_funct_1(B_4) | ~v4_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.70/1.44  tff(c_157, plain, (![A_102, B_103, D_104]: (k1_funct_1(k12_pralg_1(A_102, B_103), D_104)=u1_struct_0(k1_funct_1(B_103, D_104)) | ~r2_hidden(D_104, A_102) | ~v1_partfun1(k12_pralg_1(A_102, B_103), A_102) | ~v1_funct_1(k12_pralg_1(A_102, B_103)) | ~v4_relat_1(k12_pralg_1(A_102, B_103), A_102) | ~v1_relat_1(k12_pralg_1(A_102, B_103)) | ~v2_pralg_1(B_103) | ~v1_partfun1(B_103, A_102) | ~v1_funct_1(B_103) | ~v4_relat_1(B_103, A_102) | ~v1_relat_1(B_103) | ~r2_hidden(D_104, A_102) | ~v2_pralg_1(B_103) | ~v1_partfun1(B_103, A_102) | ~v1_funct_1(B_103) | ~v4_relat_1(B_103, A_102) | ~v1_relat_1(B_103))), inference(superposition, [status(thm), theory('equality')], [c_101, c_8])).
% 2.70/1.44  tff(c_162, plain, (![A_106, B_107, D_108]: (k1_funct_1(k12_pralg_1(A_106, B_107), D_108)=u1_struct_0(k1_funct_1(B_107, D_108)) | ~v1_partfun1(k12_pralg_1(A_106, B_107), A_106) | ~v1_funct_1(k12_pralg_1(A_106, B_107)) | ~v1_relat_1(k12_pralg_1(A_106, B_107)) | ~r2_hidden(D_108, A_106) | ~v2_pralg_1(B_107) | ~v1_partfun1(B_107, A_106) | ~v1_funct_1(B_107) | ~v4_relat_1(B_107, A_106) | ~v1_relat_1(B_107))), inference(resolution, [status(thm)], [c_18, c_157])).
% 2.70/1.44  tff(c_166, plain, (![A_109, B_110, D_111]: (k1_funct_1(k12_pralg_1(A_109, B_110), D_111)=u1_struct_0(k1_funct_1(B_110, D_111)) | ~v1_funct_1(k12_pralg_1(A_109, B_110)) | ~v1_relat_1(k12_pralg_1(A_109, B_110)) | ~r2_hidden(D_111, A_109) | ~v2_pralg_1(B_110) | ~v1_partfun1(B_110, A_109) | ~v1_funct_1(B_110) | ~v4_relat_1(B_110, A_109) | ~v1_relat_1(B_110))), inference(resolution, [status(thm)], [c_14, c_162])).
% 2.70/1.44  tff(c_170, plain, (![A_112, B_113, D_114]: (k1_funct_1(k12_pralg_1(A_112, B_113), D_114)=u1_struct_0(k1_funct_1(B_113, D_114)) | ~v1_funct_1(k12_pralg_1(A_112, B_113)) | ~r2_hidden(D_114, A_112) | ~v2_pralg_1(B_113) | ~v1_partfun1(B_113, A_112) | ~v1_funct_1(B_113) | ~v4_relat_1(B_113, A_112) | ~v1_relat_1(B_113))), inference(resolution, [status(thm)], [c_20, c_166])).
% 2.70/1.44  tff(c_174, plain, (![A_115, B_116, D_117]: (k1_funct_1(k12_pralg_1(A_115, B_116), D_117)=u1_struct_0(k1_funct_1(B_116, D_117)) | ~r2_hidden(D_117, A_115) | ~v2_pralg_1(B_116) | ~v1_partfun1(B_116, A_115) | ~v1_funct_1(B_116) | ~v4_relat_1(B_116, A_115) | ~v1_relat_1(B_116))), inference(resolution, [status(thm)], [c_16, c_170])).
% 2.70/1.44  tff(c_44, plain, (![A_48, B_49, C_50]: (k10_pralg_1(A_48, B_49, C_50)=k1_funct_1(B_49, C_50) | ~m1_subset_1(C_50, A_48) | ~v2_pralg_1(B_49) | ~v1_partfun1(B_49, A_48) | ~v1_funct_1(B_49) | ~v4_relat_1(B_49, A_48) | ~v1_relat_1(B_49) | v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.70/1.44  tff(c_46, plain, (![B_49]: (k10_pralg_1('#skF_3', B_49, '#skF_5')=k1_funct_1(B_49, '#skF_5') | ~v2_pralg_1(B_49) | ~v1_partfun1(B_49, '#skF_3') | ~v1_funct_1(B_49) | ~v4_relat_1(B_49, '#skF_3') | ~v1_relat_1(B_49) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_44])).
% 2.70/1.44  tff(c_50, plain, (![B_51]: (k10_pralg_1('#skF_3', B_51, '#skF_5')=k1_funct_1(B_51, '#skF_5') | ~v2_pralg_1(B_51) | ~v1_partfun1(B_51, '#skF_3') | ~v1_funct_1(B_51) | ~v4_relat_1(B_51, '#skF_3') | ~v1_relat_1(B_51))), inference(negUnitSimplification, [status(thm)], [c_38, c_46])).
% 2.70/1.44  tff(c_57, plain, (k10_pralg_1('#skF_3', '#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_5') | ~v2_pralg_1('#skF_4') | ~v1_partfun1('#skF_4', '#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_50])).
% 2.70/1.44  tff(c_61, plain, (k10_pralg_1('#skF_3', '#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_30, c_28, c_57])).
% 2.70/1.44  tff(c_24, plain, (k1_funct_1(k12_pralg_1('#skF_3', '#skF_4'), '#skF_5')!=u1_struct_0(k10_pralg_1('#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.70/1.44  tff(c_63, plain, (k1_funct_1(k12_pralg_1('#skF_3', '#skF_4'), '#skF_5')!=u1_struct_0(k1_funct_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_24])).
% 2.70/1.44  tff(c_186, plain, (~r2_hidden('#skF_5', '#skF_3') | ~v2_pralg_1('#skF_4') | ~v1_partfun1('#skF_4', '#skF_3') | ~v1_funct_1('#skF_4') | ~v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_174, c_63])).
% 2.70/1.44  tff(c_193, plain, (~r2_hidden('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_28, c_186])).
% 2.70/1.44  tff(c_197, plain, (v1_xboole_0('#skF_3') | ~m1_subset_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_2, c_193])).
% 2.70/1.44  tff(c_200, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_197])).
% 2.70/1.44  tff(c_202, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_200])).
% 2.70/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.44  
% 2.70/1.44  Inference rules
% 2.70/1.44  ----------------------
% 2.70/1.44  #Ref     : 0
% 2.70/1.44  #Sup     : 36
% 2.70/1.44  #Fact    : 0
% 2.70/1.44  #Define  : 0
% 2.70/1.44  #Split   : 0
% 2.70/1.44  #Chain   : 0
% 2.70/1.44  #Close   : 0
% 2.70/1.44  
% 2.70/1.44  Ordering : KBO
% 2.70/1.44  
% 2.70/1.44  Simplification rules
% 2.70/1.44  ----------------------
% 2.70/1.44  #Subsume      : 14
% 2.70/1.44  #Demod        : 15
% 2.70/1.44  #Tautology    : 8
% 2.70/1.44  #SimpNegUnit  : 3
% 2.70/1.44  #BackRed      : 1
% 2.70/1.44  
% 2.70/1.44  #Partial instantiations: 0
% 2.70/1.44  #Strategies tried      : 1
% 2.70/1.44  
% 2.70/1.44  Timing (in seconds)
% 2.70/1.44  ----------------------
% 2.70/1.44  Preprocessing        : 0.35
% 2.70/1.44  Parsing              : 0.18
% 2.70/1.44  CNF conversion       : 0.03
% 2.70/1.44  Main loop            : 0.27
% 2.70/1.44  Inferencing          : 0.11
% 2.70/1.44  Reduction            : 0.06
% 2.70/1.44  Demodulation         : 0.04
% 2.70/1.44  BG Simplification    : 0.02
% 2.70/1.44  Subsumption          : 0.06
% 2.70/1.44  Abstraction          : 0.01
% 2.70/1.44  MUC search           : 0.00
% 2.70/1.44  Cooper               : 0.00
% 2.70/1.44  Total                : 0.65
% 2.70/1.44  Index Insertion      : 0.00
% 2.70/1.44  Index Deletion       : 0.00
% 2.70/1.44  Index Matching       : 0.00
% 2.70/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
