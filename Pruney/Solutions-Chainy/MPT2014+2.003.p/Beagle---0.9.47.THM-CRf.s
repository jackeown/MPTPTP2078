%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:09 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 103 expanded)
%              Number of leaves         :   32 (  52 expanded)
%              Depth                    :   14
%              Number of atoms          :  188 ( 307 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_xboole_0 > v1_funct_1 > l1_struct_0 > k4_waybel_9 > a_3_0_waybel_9 > u1_waybel_0 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k4_waybel_9,type,(
    k4_waybel_9: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(u1_waybel_0,type,(
    u1_waybel_0: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(a_3_0_waybel_9,type,(
    a_3_0_waybel_9: ( $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_waybel_0(B,A) )
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(B))
               => r1_tarski(u1_struct_0(k4_waybel_9(A,B,C)),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_waybel_9)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v2_struct_0(B)
        & l1_struct_0(B)
        & ~ v2_struct_0(C)
        & l1_waybel_0(C,B)
        & m1_subset_1(D,u1_struct_0(C)) )
     => ( r2_hidden(A,a_3_0_waybel_9(B,C,D))
      <=> ? [E] :
            ( m1_subset_1(E,u1_struct_0(C))
            & A = E
            & r1_orders_2(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_3_0_waybel_9)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_109,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => u1_struct_0(k4_waybel_9(A,B,C)) = a_3_0_waybel_9(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_waybel_9)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_waybel_0(B,A) )
     => ( v1_funct_1(u1_waybel_0(A,B))
        & v1_funct_2(u1_waybel_0(A,B),u1_struct_0(B),u1_struct_0(A))
        & m1_subset_1(u1_waybel_0(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A) )
     => ( v1_funct_1(u1_waybel_0(A,B))
        & ~ v1_xboole_0(u1_waybel_0(A,B))
        & v1_funct_2(u1_waybel_0(A,B),u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc15_yellow_6)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_42,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_38,plain,(
    l1_waybel_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_52,plain,(
    ! [A_38,B_39] :
      ( r2_hidden('#skF_1'(A_38,B_39),A_38)
      | r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_57,plain,(
    ! [A_38] : r1_tarski(A_38,A_38) ),
    inference(resolution,[status(thm)],[c_52,c_4])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,(
    ! [C_40,B_41,A_42] :
      ( r2_hidden(C_40,B_41)
      | ~ r2_hidden(C_40,A_42)
      | ~ r1_tarski(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_63,plain,(
    ! [A_1,B_2,B_41] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_41)
      | ~ r1_tarski(A_1,B_41)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_58])).

tff(c_136,plain,(
    ! [A_75,B_76,C_77,D_78] :
      ( '#skF_2'(A_75,B_76,C_77,D_78) = A_75
      | ~ r2_hidden(A_75,a_3_0_waybel_9(B_76,C_77,D_78))
      | ~ m1_subset_1(D_78,u1_struct_0(C_77))
      | ~ l1_waybel_0(C_77,B_76)
      | v2_struct_0(C_77)
      | ~ l1_struct_0(B_76)
      | v2_struct_0(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_199,plain,(
    ! [B_110,C_111,D_112,B_113] :
      ( '#skF_2'('#skF_1'(a_3_0_waybel_9(B_110,C_111,D_112),B_113),B_110,C_111,D_112) = '#skF_1'(a_3_0_waybel_9(B_110,C_111,D_112),B_113)
      | ~ m1_subset_1(D_112,u1_struct_0(C_111))
      | ~ l1_waybel_0(C_111,B_110)
      | v2_struct_0(C_111)
      | ~ l1_struct_0(B_110)
      | v2_struct_0(B_110)
      | r1_tarski(a_3_0_waybel_9(B_110,C_111,D_112),B_113) ) ),
    inference(resolution,[status(thm)],[c_6,c_136])).

tff(c_30,plain,(
    ! [A_16,B_17,C_18,D_19] :
      ( m1_subset_1('#skF_2'(A_16,B_17,C_18,D_19),u1_struct_0(C_18))
      | ~ r2_hidden(A_16,a_3_0_waybel_9(B_17,C_18,D_19))
      | ~ m1_subset_1(D_19,u1_struct_0(C_18))
      | ~ l1_waybel_0(C_18,B_17)
      | v2_struct_0(C_18)
      | ~ l1_struct_0(B_17)
      | v2_struct_0(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_672,plain,(
    ! [B_206,C_207,D_208,B_209] :
      ( m1_subset_1('#skF_1'(a_3_0_waybel_9(B_206,C_207,D_208),B_209),u1_struct_0(C_207))
      | ~ r2_hidden('#skF_1'(a_3_0_waybel_9(B_206,C_207,D_208),B_209),a_3_0_waybel_9(B_206,C_207,D_208))
      | ~ m1_subset_1(D_208,u1_struct_0(C_207))
      | ~ l1_waybel_0(C_207,B_206)
      | v2_struct_0(C_207)
      | ~ l1_struct_0(B_206)
      | v2_struct_0(B_206)
      | ~ m1_subset_1(D_208,u1_struct_0(C_207))
      | ~ l1_waybel_0(C_207,B_206)
      | v2_struct_0(C_207)
      | ~ l1_struct_0(B_206)
      | v2_struct_0(B_206)
      | r1_tarski(a_3_0_waybel_9(B_206,C_207,D_208),B_209) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_30])).

tff(c_680,plain,(
    ! [B_206,C_207,D_208,B_2] :
      ( m1_subset_1('#skF_1'(a_3_0_waybel_9(B_206,C_207,D_208),B_2),u1_struct_0(C_207))
      | ~ m1_subset_1(D_208,u1_struct_0(C_207))
      | ~ l1_waybel_0(C_207,B_206)
      | v2_struct_0(C_207)
      | ~ l1_struct_0(B_206)
      | v2_struct_0(B_206)
      | ~ r1_tarski(a_3_0_waybel_9(B_206,C_207,D_208),a_3_0_waybel_9(B_206,C_207,D_208))
      | r1_tarski(a_3_0_waybel_9(B_206,C_207,D_208),B_2) ) ),
    inference(resolution,[status(thm)],[c_63,c_672])).

tff(c_694,plain,(
    ! [B_210,C_211,D_212,B_213] :
      ( m1_subset_1('#skF_1'(a_3_0_waybel_9(B_210,C_211,D_212),B_213),u1_struct_0(C_211))
      | ~ m1_subset_1(D_212,u1_struct_0(C_211))
      | ~ l1_waybel_0(C_211,B_210)
      | v2_struct_0(C_211)
      | ~ l1_struct_0(B_210)
      | v2_struct_0(B_210)
      | r1_tarski(a_3_0_waybel_9(B_210,C_211,D_212),B_213) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_680])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | v1_xboole_0(B_7)
      | ~ m1_subset_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_46,plain,(
    ! [A_36,B_37] :
      ( ~ r2_hidden('#skF_1'(A_36,B_37),B_37)
      | r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_51,plain,(
    ! [A_36,B_7] :
      ( r1_tarski(A_36,B_7)
      | v1_xboole_0(B_7)
      | ~ m1_subset_1('#skF_1'(A_36,B_7),B_7) ) ),
    inference(resolution,[status(thm)],[c_8,c_46])).

tff(c_732,plain,(
    ! [C_214,D_215,B_216] :
      ( v1_xboole_0(u1_struct_0(C_214))
      | ~ m1_subset_1(D_215,u1_struct_0(C_214))
      | ~ l1_waybel_0(C_214,B_216)
      | v2_struct_0(C_214)
      | ~ l1_struct_0(B_216)
      | v2_struct_0(B_216)
      | r1_tarski(a_3_0_waybel_9(B_216,C_214,D_215),u1_struct_0(C_214)) ) ),
    inference(resolution,[status(thm)],[c_694,c_51])).

tff(c_99,plain,(
    ! [A_71,B_72,C_73] :
      ( u1_struct_0(k4_waybel_9(A_71,B_72,C_73)) = a_3_0_waybel_9(A_71,B_72,C_73)
      | ~ m1_subset_1(C_73,u1_struct_0(B_72))
      | ~ l1_waybel_0(B_72,A_71)
      | v2_struct_0(B_72)
      | ~ l1_struct_0(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_101,plain,(
    ! [A_71] :
      ( u1_struct_0(k4_waybel_9(A_71,'#skF_4','#skF_5')) = a_3_0_waybel_9(A_71,'#skF_4','#skF_5')
      | ~ l1_waybel_0('#skF_4',A_71)
      | v2_struct_0('#skF_4')
      | ~ l1_struct_0(A_71)
      | v2_struct_0(A_71) ) ),
    inference(resolution,[status(thm)],[c_36,c_99])).

tff(c_105,plain,(
    ! [A_74] :
      ( u1_struct_0(k4_waybel_9(A_74,'#skF_4','#skF_5')) = a_3_0_waybel_9(A_74,'#skF_4','#skF_5')
      | ~ l1_waybel_0('#skF_4',A_74)
      | ~ l1_struct_0(A_74)
      | v2_struct_0(A_74) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_101])).

tff(c_34,plain,(
    ~ r1_tarski(u1_struct_0(k4_waybel_9('#skF_3','#skF_4','#skF_5')),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_127,plain,
    ( ~ r1_tarski(a_3_0_waybel_9('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_4'))
    | ~ l1_waybel_0('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_34])).

tff(c_133,plain,
    ( ~ r1_tarski(a_3_0_waybel_9('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_127])).

tff(c_134,plain,(
    ~ r1_tarski(a_3_0_waybel_9('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_133])).

tff(c_737,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_waybel_0('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_732,c_134])).

tff(c_754,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_36,c_737])).

tff(c_755,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_40,c_754])).

tff(c_88,plain,(
    ! [A_65,B_66] :
      ( m1_subset_1(u1_waybel_0(A_65,B_66),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_66),u1_struct_0(A_65))))
      | ~ l1_waybel_0(B_66,A_65)
      | ~ l1_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [C_11,A_8,B_9] :
      ( v1_xboole_0(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_93,plain,(
    ! [A_67,B_68] :
      ( v1_xboole_0(u1_waybel_0(A_67,B_68))
      | ~ v1_xboole_0(u1_struct_0(B_68))
      | ~ l1_waybel_0(B_68,A_67)
      | ~ l1_struct_0(A_67) ) ),
    inference(resolution,[status(thm)],[c_88,c_10])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( ~ v1_xboole_0(u1_waybel_0(A_14,B_15))
      | ~ l1_waybel_0(B_15,A_14)
      | v2_struct_0(B_15)
      | ~ l1_struct_0(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_97,plain,(
    ! [B_68,A_67] :
      ( v2_struct_0(B_68)
      | v2_struct_0(A_67)
      | ~ v1_xboole_0(u1_struct_0(B_68))
      | ~ l1_waybel_0(B_68,A_67)
      | ~ l1_struct_0(A_67) ) ),
    inference(resolution,[status(thm)],[c_93,c_20])).

tff(c_759,plain,(
    ! [A_67] :
      ( v2_struct_0('#skF_4')
      | v2_struct_0(A_67)
      | ~ l1_waybel_0('#skF_4',A_67)
      | ~ l1_struct_0(A_67) ) ),
    inference(resolution,[status(thm)],[c_755,c_97])).

tff(c_763,plain,(
    ! [A_217] :
      ( v2_struct_0(A_217)
      | ~ l1_waybel_0('#skF_4',A_217)
      | ~ l1_struct_0(A_217) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_759])).

tff(c_766,plain,
    ( v2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_763])).

tff(c_769,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_766])).

tff(c_771,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_769])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:55:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.45/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/1.61  
% 3.80/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/1.62  %$ v1_funct_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_xboole_0 > v1_funct_1 > l1_struct_0 > k4_waybel_9 > a_3_0_waybel_9 > u1_waybel_0 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.80/1.62  
% 3.80/1.62  %Foreground sorts:
% 3.80/1.62  
% 3.80/1.62  
% 3.80/1.62  %Background operators:
% 3.80/1.62  
% 3.80/1.62  
% 3.80/1.62  %Foreground operators:
% 3.80/1.62  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.80/1.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.80/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.80/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.80/1.62  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.80/1.62  tff(k4_waybel_9, type, k4_waybel_9: ($i * $i * $i) > $i).
% 3.80/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.80/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.80/1.62  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.80/1.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.80/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.80/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.80/1.62  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.80/1.62  tff(u1_waybel_0, type, u1_waybel_0: ($i * $i) > $i).
% 3.80/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.80/1.62  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 3.80/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.80/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.80/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.80/1.62  tff(a_3_0_waybel_9, type, a_3_0_waybel_9: ($i * $i * $i) > $i).
% 3.80/1.62  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.80/1.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.80/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.80/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.80/1.62  
% 3.80/1.63  tff(f_126, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => r1_tarski(u1_struct_0(k4_waybel_9(A, B, C)), u1_struct_0(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_waybel_9)).
% 3.80/1.63  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.80/1.63  tff(f_93, axiom, (![A, B, C, D]: (((((~v2_struct_0(B) & l1_struct_0(B)) & ~v2_struct_0(C)) & l1_waybel_0(C, B)) & m1_subset_1(D, u1_struct_0(C))) => (r2_hidden(A, a_3_0_waybel_9(B, C, D)) <=> (?[E]: ((m1_subset_1(E, u1_struct_0(C)) & (A = E)) & r1_orders_2(C, D, E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_3_0_waybel_9)).
% 3.80/1.63  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.80/1.63  tff(f_109, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => (u1_struct_0(k4_waybel_9(A, B, C)) = a_3_0_waybel_9(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_waybel_9)).
% 3.80/1.63  tff(f_55, axiom, (![A, B]: ((l1_struct_0(A) & l1_waybel_0(B, A)) => ((v1_funct_1(u1_waybel_0(A, B)) & v1_funct_2(u1_waybel_0(A, B), u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(u1_waybel_0(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_waybel_0)).
% 3.80/1.63  tff(f_45, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 3.80/1.63  tff(f_72, axiom, (![A, B]: ((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & l1_waybel_0(B, A)) => ((v1_funct_1(u1_waybel_0(A, B)) & ~v1_xboole_0(u1_waybel_0(A, B))) & v1_funct_2(u1_waybel_0(A, B), u1_struct_0(B), u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc15_yellow_6)).
% 3.80/1.63  tff(c_44, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.80/1.63  tff(c_42, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.80/1.63  tff(c_38, plain, (l1_waybel_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.80/1.63  tff(c_40, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.80/1.63  tff(c_36, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.80/1.63  tff(c_52, plain, (![A_38, B_39]: (r2_hidden('#skF_1'(A_38, B_39), A_38) | r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.80/1.63  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.80/1.63  tff(c_57, plain, (![A_38]: (r1_tarski(A_38, A_38))), inference(resolution, [status(thm)], [c_52, c_4])).
% 3.80/1.63  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.80/1.63  tff(c_58, plain, (![C_40, B_41, A_42]: (r2_hidden(C_40, B_41) | ~r2_hidden(C_40, A_42) | ~r1_tarski(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.80/1.63  tff(c_63, plain, (![A_1, B_2, B_41]: (r2_hidden('#skF_1'(A_1, B_2), B_41) | ~r1_tarski(A_1, B_41) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_58])).
% 3.80/1.63  tff(c_136, plain, (![A_75, B_76, C_77, D_78]: ('#skF_2'(A_75, B_76, C_77, D_78)=A_75 | ~r2_hidden(A_75, a_3_0_waybel_9(B_76, C_77, D_78)) | ~m1_subset_1(D_78, u1_struct_0(C_77)) | ~l1_waybel_0(C_77, B_76) | v2_struct_0(C_77) | ~l1_struct_0(B_76) | v2_struct_0(B_76))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.80/1.63  tff(c_199, plain, (![B_110, C_111, D_112, B_113]: ('#skF_2'('#skF_1'(a_3_0_waybel_9(B_110, C_111, D_112), B_113), B_110, C_111, D_112)='#skF_1'(a_3_0_waybel_9(B_110, C_111, D_112), B_113) | ~m1_subset_1(D_112, u1_struct_0(C_111)) | ~l1_waybel_0(C_111, B_110) | v2_struct_0(C_111) | ~l1_struct_0(B_110) | v2_struct_0(B_110) | r1_tarski(a_3_0_waybel_9(B_110, C_111, D_112), B_113))), inference(resolution, [status(thm)], [c_6, c_136])).
% 3.80/1.63  tff(c_30, plain, (![A_16, B_17, C_18, D_19]: (m1_subset_1('#skF_2'(A_16, B_17, C_18, D_19), u1_struct_0(C_18)) | ~r2_hidden(A_16, a_3_0_waybel_9(B_17, C_18, D_19)) | ~m1_subset_1(D_19, u1_struct_0(C_18)) | ~l1_waybel_0(C_18, B_17) | v2_struct_0(C_18) | ~l1_struct_0(B_17) | v2_struct_0(B_17))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.80/1.63  tff(c_672, plain, (![B_206, C_207, D_208, B_209]: (m1_subset_1('#skF_1'(a_3_0_waybel_9(B_206, C_207, D_208), B_209), u1_struct_0(C_207)) | ~r2_hidden('#skF_1'(a_3_0_waybel_9(B_206, C_207, D_208), B_209), a_3_0_waybel_9(B_206, C_207, D_208)) | ~m1_subset_1(D_208, u1_struct_0(C_207)) | ~l1_waybel_0(C_207, B_206) | v2_struct_0(C_207) | ~l1_struct_0(B_206) | v2_struct_0(B_206) | ~m1_subset_1(D_208, u1_struct_0(C_207)) | ~l1_waybel_0(C_207, B_206) | v2_struct_0(C_207) | ~l1_struct_0(B_206) | v2_struct_0(B_206) | r1_tarski(a_3_0_waybel_9(B_206, C_207, D_208), B_209))), inference(superposition, [status(thm), theory('equality')], [c_199, c_30])).
% 3.80/1.63  tff(c_680, plain, (![B_206, C_207, D_208, B_2]: (m1_subset_1('#skF_1'(a_3_0_waybel_9(B_206, C_207, D_208), B_2), u1_struct_0(C_207)) | ~m1_subset_1(D_208, u1_struct_0(C_207)) | ~l1_waybel_0(C_207, B_206) | v2_struct_0(C_207) | ~l1_struct_0(B_206) | v2_struct_0(B_206) | ~r1_tarski(a_3_0_waybel_9(B_206, C_207, D_208), a_3_0_waybel_9(B_206, C_207, D_208)) | r1_tarski(a_3_0_waybel_9(B_206, C_207, D_208), B_2))), inference(resolution, [status(thm)], [c_63, c_672])).
% 3.80/1.63  tff(c_694, plain, (![B_210, C_211, D_212, B_213]: (m1_subset_1('#skF_1'(a_3_0_waybel_9(B_210, C_211, D_212), B_213), u1_struct_0(C_211)) | ~m1_subset_1(D_212, u1_struct_0(C_211)) | ~l1_waybel_0(C_211, B_210) | v2_struct_0(C_211) | ~l1_struct_0(B_210) | v2_struct_0(B_210) | r1_tarski(a_3_0_waybel_9(B_210, C_211, D_212), B_213))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_680])).
% 3.80/1.63  tff(c_8, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | v1_xboole_0(B_7) | ~m1_subset_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.80/1.63  tff(c_46, plain, (![A_36, B_37]: (~r2_hidden('#skF_1'(A_36, B_37), B_37) | r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.80/1.63  tff(c_51, plain, (![A_36, B_7]: (r1_tarski(A_36, B_7) | v1_xboole_0(B_7) | ~m1_subset_1('#skF_1'(A_36, B_7), B_7))), inference(resolution, [status(thm)], [c_8, c_46])).
% 3.80/1.63  tff(c_732, plain, (![C_214, D_215, B_216]: (v1_xboole_0(u1_struct_0(C_214)) | ~m1_subset_1(D_215, u1_struct_0(C_214)) | ~l1_waybel_0(C_214, B_216) | v2_struct_0(C_214) | ~l1_struct_0(B_216) | v2_struct_0(B_216) | r1_tarski(a_3_0_waybel_9(B_216, C_214, D_215), u1_struct_0(C_214)))), inference(resolution, [status(thm)], [c_694, c_51])).
% 3.80/1.63  tff(c_99, plain, (![A_71, B_72, C_73]: (u1_struct_0(k4_waybel_9(A_71, B_72, C_73))=a_3_0_waybel_9(A_71, B_72, C_73) | ~m1_subset_1(C_73, u1_struct_0(B_72)) | ~l1_waybel_0(B_72, A_71) | v2_struct_0(B_72) | ~l1_struct_0(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.80/1.63  tff(c_101, plain, (![A_71]: (u1_struct_0(k4_waybel_9(A_71, '#skF_4', '#skF_5'))=a_3_0_waybel_9(A_71, '#skF_4', '#skF_5') | ~l1_waybel_0('#skF_4', A_71) | v2_struct_0('#skF_4') | ~l1_struct_0(A_71) | v2_struct_0(A_71))), inference(resolution, [status(thm)], [c_36, c_99])).
% 3.80/1.63  tff(c_105, plain, (![A_74]: (u1_struct_0(k4_waybel_9(A_74, '#skF_4', '#skF_5'))=a_3_0_waybel_9(A_74, '#skF_4', '#skF_5') | ~l1_waybel_0('#skF_4', A_74) | ~l1_struct_0(A_74) | v2_struct_0(A_74))), inference(negUnitSimplification, [status(thm)], [c_40, c_101])).
% 3.80/1.63  tff(c_34, plain, (~r1_tarski(u1_struct_0(k4_waybel_9('#skF_3', '#skF_4', '#skF_5')), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.80/1.63  tff(c_127, plain, (~r1_tarski(a_3_0_waybel_9('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_4')) | ~l1_waybel_0('#skF_4', '#skF_3') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_105, c_34])).
% 3.80/1.63  tff(c_133, plain, (~r1_tarski(a_3_0_waybel_9('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_127])).
% 3.80/1.63  tff(c_134, plain, (~r1_tarski(a_3_0_waybel_9('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_44, c_133])).
% 3.80/1.63  tff(c_737, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_waybel_0('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_732, c_134])).
% 3.80/1.63  tff(c_754, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_36, c_737])).
% 3.80/1.63  tff(c_755, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_44, c_40, c_754])).
% 3.80/1.63  tff(c_88, plain, (![A_65, B_66]: (m1_subset_1(u1_waybel_0(A_65, B_66), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_66), u1_struct_0(A_65)))) | ~l1_waybel_0(B_66, A_65) | ~l1_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.80/1.63  tff(c_10, plain, (![C_11, A_8, B_9]: (v1_xboole_0(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.80/1.63  tff(c_93, plain, (![A_67, B_68]: (v1_xboole_0(u1_waybel_0(A_67, B_68)) | ~v1_xboole_0(u1_struct_0(B_68)) | ~l1_waybel_0(B_68, A_67) | ~l1_struct_0(A_67))), inference(resolution, [status(thm)], [c_88, c_10])).
% 3.80/1.63  tff(c_20, plain, (![A_14, B_15]: (~v1_xboole_0(u1_waybel_0(A_14, B_15)) | ~l1_waybel_0(B_15, A_14) | v2_struct_0(B_15) | ~l1_struct_0(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.80/1.63  tff(c_97, plain, (![B_68, A_67]: (v2_struct_0(B_68) | v2_struct_0(A_67) | ~v1_xboole_0(u1_struct_0(B_68)) | ~l1_waybel_0(B_68, A_67) | ~l1_struct_0(A_67))), inference(resolution, [status(thm)], [c_93, c_20])).
% 3.80/1.63  tff(c_759, plain, (![A_67]: (v2_struct_0('#skF_4') | v2_struct_0(A_67) | ~l1_waybel_0('#skF_4', A_67) | ~l1_struct_0(A_67))), inference(resolution, [status(thm)], [c_755, c_97])).
% 3.80/1.63  tff(c_763, plain, (![A_217]: (v2_struct_0(A_217) | ~l1_waybel_0('#skF_4', A_217) | ~l1_struct_0(A_217))), inference(negUnitSimplification, [status(thm)], [c_40, c_759])).
% 3.80/1.63  tff(c_766, plain, (v2_struct_0('#skF_3') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_763])).
% 3.80/1.63  tff(c_769, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_766])).
% 3.80/1.63  tff(c_771, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_769])).
% 3.80/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/1.63  
% 3.80/1.63  Inference rules
% 3.80/1.63  ----------------------
% 3.80/1.63  #Ref     : 0
% 3.80/1.63  #Sup     : 185
% 3.80/1.63  #Fact    : 0
% 3.80/1.63  #Define  : 0
% 3.80/1.63  #Split   : 1
% 3.80/1.63  #Chain   : 0
% 3.80/1.63  #Close   : 0
% 3.80/1.63  
% 3.80/1.63  Ordering : KBO
% 3.80/1.63  
% 3.80/1.63  Simplification rules
% 3.80/1.63  ----------------------
% 3.80/1.63  #Subsume      : 36
% 3.80/1.63  #Demod        : 12
% 3.80/1.63  #Tautology    : 19
% 3.80/1.63  #SimpNegUnit  : 23
% 3.80/1.63  #BackRed      : 0
% 3.80/1.63  
% 3.80/1.63  #Partial instantiations: 0
% 3.80/1.63  #Strategies tried      : 1
% 3.80/1.63  
% 3.80/1.63  Timing (in seconds)
% 3.80/1.63  ----------------------
% 3.80/1.63  Preprocessing        : 0.31
% 3.80/1.63  Parsing              : 0.17
% 3.80/1.63  CNF conversion       : 0.02
% 3.80/1.63  Main loop            : 0.54
% 3.80/1.63  Inferencing          : 0.22
% 3.80/1.64  Reduction            : 0.12
% 3.80/1.64  Demodulation         : 0.08
% 3.80/1.64  BG Simplification    : 0.03
% 3.80/1.64  Subsumption          : 0.13
% 3.80/1.64  Abstraction          : 0.04
% 3.80/1.64  MUC search           : 0.00
% 3.80/1.64  Cooper               : 0.00
% 3.80/1.64  Total                : 0.88
% 3.80/1.64  Index Insertion      : 0.00
% 3.80/1.64  Index Deletion       : 0.00
% 3.80/1.64  Index Matching       : 0.00
% 3.80/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
