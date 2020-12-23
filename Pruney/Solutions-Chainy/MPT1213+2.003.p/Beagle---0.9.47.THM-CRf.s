%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:19 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 232 expanded)
%              Number of leaves         :   25 ( 101 expanded)
%              Depth                    :   10
%              Number of atoms          :  263 ( 932 expanded)
%              Number of equality atoms :   55 ( 125 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattices > m1_subset_1 > v2_struct_0 > v17_lattices > v16_lattices > v15_lattices > v11_lattices > v10_lattices > l3_lattices > k2_lattices > k1_lattices > k7_lattices > #nlpp > u1_struct_0 > k6_lattices > k5_lattices > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(k6_lattices,type,(
    k6_lattices: $i > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k2_lattices,type,(
    k2_lattices: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_lattices,type,(
    k1_lattices: ( $i * $i * $i ) > $i )).

tff(r2_lattices,type,(
    r2_lattices: ( $i * $i * $i ) > $o )).

tff(v17_lattices,type,(
    v17_lattices: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v11_lattices,type,(
    v11_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_lattices,type,(
    k5_lattices: $i > $i )).

tff(k7_lattices,type,(
    k7_lattices: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v16_lattices,type,(
    v16_lattices: $i > $o )).

tff(v15_lattices,type,(
    v15_lattices: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_112,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v17_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => k7_lattices(A,k7_lattices(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_lattices)).

tff(f_41,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( ( ~ v2_struct_0(A)
          & v17_lattices(A) )
       => ( ~ v2_struct_0(A)
          & v11_lattices(A)
          & v15_lattices(A)
          & v16_lattices(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_lattices)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k7_lattices(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattices)).

tff(f_88,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( ( ~ v2_struct_0(A)
              & v10_lattices(A)
              & v11_lattices(A)
              & v16_lattices(A)
              & l3_lattices(A) )
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( C = k7_lattices(A,B)
                <=> r2_lattices(A,C,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattices)).

tff(f_62,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_lattices(A,B,C)
              <=> ( k1_lattices(A,B,C) = k6_lattices(A)
                  & k1_lattices(A,C,B) = k6_lattices(A)
                  & k2_lattices(A,B,C) = k5_lattices(A)
                  & k2_lattices(A,C,B) = k5_lattices(A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_lattices)).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_26,plain,(
    k7_lattices('#skF_1',k7_lattices('#skF_1','#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_30,plain,(
    l3_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_34,plain,(
    v10_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_32,plain,(
    v17_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_37,plain,(
    ! [A_19] :
      ( v11_lattices(A_19)
      | ~ v17_lattices(A_19)
      | v2_struct_0(A_19)
      | ~ l3_lattices(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_40,plain,
    ( v11_lattices('#skF_1')
    | ~ v17_lattices('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_37,c_36])).

tff(c_43,plain,(
    v11_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_40])).

tff(c_51,plain,(
    ! [A_21] :
      ( v16_lattices(A_21)
      | ~ v17_lattices(A_21)
      | v2_struct_0(A_21)
      | ~ l3_lattices(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_54,plain,
    ( v16_lattices('#skF_1')
    | ~ v17_lattices('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_51,c_36])).

tff(c_57,plain,(
    v16_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_54])).

tff(c_24,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k7_lattices(A_16,B_17),u1_struct_0(A_16))
      | ~ m1_subset_1(B_17,u1_struct_0(A_16))
      | ~ l3_lattices(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_64,plain,(
    ! [A_39,B_40] :
      ( r2_lattices(A_39,k7_lattices(A_39,B_40),B_40)
      | ~ m1_subset_1(k7_lattices(A_39,B_40),u1_struct_0(A_39))
      | ~ v16_lattices(A_39)
      | ~ v11_lattices(A_39)
      | ~ v10_lattices(A_39)
      | ~ m1_subset_1(B_40,u1_struct_0(A_39))
      | ~ l3_lattices(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_78,plain,(
    ! [A_44,B_45] :
      ( r2_lattices(A_44,k7_lattices(A_44,B_45),B_45)
      | ~ v16_lattices(A_44)
      | ~ v11_lattices(A_44)
      | ~ v10_lattices(A_44)
      | ~ m1_subset_1(B_45,u1_struct_0(A_44))
      | ~ l3_lattices(A_44)
      | v2_struct_0(A_44) ) ),
    inference(resolution,[status(thm)],[c_24,c_64])).

tff(c_16,plain,(
    ! [A_2,C_8,B_6] :
      ( k1_lattices(A_2,C_8,B_6) = k6_lattices(A_2)
      | ~ r2_lattices(A_2,B_6,C_8)
      | ~ m1_subset_1(C_8,u1_struct_0(A_2))
      | ~ m1_subset_1(B_6,u1_struct_0(A_2))
      | ~ l3_lattices(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_95,plain,(
    ! [A_46,B_47] :
      ( k1_lattices(A_46,B_47,k7_lattices(A_46,B_47)) = k6_lattices(A_46)
      | ~ m1_subset_1(k7_lattices(A_46,B_47),u1_struct_0(A_46))
      | ~ v16_lattices(A_46)
      | ~ v11_lattices(A_46)
      | ~ v10_lattices(A_46)
      | ~ m1_subset_1(B_47,u1_struct_0(A_46))
      | ~ l3_lattices(A_46)
      | v2_struct_0(A_46) ) ),
    inference(resolution,[status(thm)],[c_78,c_16])).

tff(c_99,plain,(
    ! [A_48,B_49] :
      ( k1_lattices(A_48,B_49,k7_lattices(A_48,B_49)) = k6_lattices(A_48)
      | ~ v16_lattices(A_48)
      | ~ v11_lattices(A_48)
      | ~ v10_lattices(A_48)
      | ~ m1_subset_1(B_49,u1_struct_0(A_48))
      | ~ l3_lattices(A_48)
      | v2_struct_0(A_48) ) ),
    inference(resolution,[status(thm)],[c_24,c_95])).

tff(c_103,plain,
    ( k1_lattices('#skF_1','#skF_2',k7_lattices('#skF_1','#skF_2')) = k6_lattices('#skF_1')
    | ~ v16_lattices('#skF_1')
    | ~ v11_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_99])).

tff(c_107,plain,
    ( k1_lattices('#skF_1','#skF_2',k7_lattices('#skF_1','#skF_2')) = k6_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34,c_43,c_57,c_103])).

tff(c_108,plain,(
    k1_lattices('#skF_1','#skF_2',k7_lattices('#skF_1','#skF_2')) = k6_lattices('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_107])).

tff(c_18,plain,(
    ! [A_2,B_6,C_8] :
      ( k1_lattices(A_2,B_6,C_8) = k6_lattices(A_2)
      | ~ r2_lattices(A_2,B_6,C_8)
      | ~ m1_subset_1(C_8,u1_struct_0(A_2))
      | ~ m1_subset_1(B_6,u1_struct_0(A_2))
      | ~ l3_lattices(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_194,plain,(
    ! [A_60,B_61] :
      ( k1_lattices(A_60,k7_lattices(A_60,B_61),B_61) = k6_lattices(A_60)
      | ~ m1_subset_1(k7_lattices(A_60,B_61),u1_struct_0(A_60))
      | ~ v16_lattices(A_60)
      | ~ v11_lattices(A_60)
      | ~ v10_lattices(A_60)
      | ~ m1_subset_1(B_61,u1_struct_0(A_60))
      | ~ l3_lattices(A_60)
      | v2_struct_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_78,c_18])).

tff(c_198,plain,(
    ! [A_62,B_63] :
      ( k1_lattices(A_62,k7_lattices(A_62,B_63),B_63) = k6_lattices(A_62)
      | ~ v16_lattices(A_62)
      | ~ v11_lattices(A_62)
      | ~ v10_lattices(A_62)
      | ~ m1_subset_1(B_63,u1_struct_0(A_62))
      | ~ l3_lattices(A_62)
      | v2_struct_0(A_62) ) ),
    inference(resolution,[status(thm)],[c_24,c_194])).

tff(c_202,plain,
    ( k1_lattices('#skF_1',k7_lattices('#skF_1','#skF_2'),'#skF_2') = k6_lattices('#skF_1')
    | ~ v16_lattices('#skF_1')
    | ~ v11_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_198])).

tff(c_206,plain,
    ( k1_lattices('#skF_1',k7_lattices('#skF_1','#skF_2'),'#skF_2') = k6_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34,c_43,c_57,c_202])).

tff(c_207,plain,(
    k1_lattices('#skF_1',k7_lattices('#skF_1','#skF_2'),'#skF_2') = k6_lattices('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_206])).

tff(c_12,plain,(
    ! [A_2,C_8,B_6] :
      ( k2_lattices(A_2,C_8,B_6) = k5_lattices(A_2)
      | ~ r2_lattices(A_2,B_6,C_8)
      | ~ m1_subset_1(C_8,u1_struct_0(A_2))
      | ~ m1_subset_1(B_6,u1_struct_0(A_2))
      | ~ l3_lattices(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_136,plain,(
    ! [A_53,B_54] :
      ( k2_lattices(A_53,B_54,k7_lattices(A_53,B_54)) = k5_lattices(A_53)
      | ~ m1_subset_1(k7_lattices(A_53,B_54),u1_struct_0(A_53))
      | ~ v16_lattices(A_53)
      | ~ v11_lattices(A_53)
      | ~ v10_lattices(A_53)
      | ~ m1_subset_1(B_54,u1_struct_0(A_53))
      | ~ l3_lattices(A_53)
      | v2_struct_0(A_53) ) ),
    inference(resolution,[status(thm)],[c_78,c_12])).

tff(c_171,plain,(
    ! [A_56,B_57] :
      ( k2_lattices(A_56,B_57,k7_lattices(A_56,B_57)) = k5_lattices(A_56)
      | ~ v16_lattices(A_56)
      | ~ v11_lattices(A_56)
      | ~ v10_lattices(A_56)
      | ~ m1_subset_1(B_57,u1_struct_0(A_56))
      | ~ l3_lattices(A_56)
      | v2_struct_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_24,c_136])).

tff(c_175,plain,
    ( k2_lattices('#skF_1','#skF_2',k7_lattices('#skF_1','#skF_2')) = k5_lattices('#skF_1')
    | ~ v16_lattices('#skF_1')
    | ~ v11_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_171])).

tff(c_179,plain,
    ( k2_lattices('#skF_1','#skF_2',k7_lattices('#skF_1','#skF_2')) = k5_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34,c_43,c_57,c_175])).

tff(c_180,plain,(
    k2_lattices('#skF_1','#skF_2',k7_lattices('#skF_1','#skF_2')) = k5_lattices('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_179])).

tff(c_14,plain,(
    ! [A_2,B_6,C_8] :
      ( k2_lattices(A_2,B_6,C_8) = k5_lattices(A_2)
      | ~ r2_lattices(A_2,B_6,C_8)
      | ~ m1_subset_1(C_8,u1_struct_0(A_2))
      | ~ m1_subset_1(B_6,u1_struct_0(A_2))
      | ~ l3_lattices(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_237,plain,(
    ! [A_69,B_70] :
      ( k2_lattices(A_69,k7_lattices(A_69,B_70),B_70) = k5_lattices(A_69)
      | ~ m1_subset_1(k7_lattices(A_69,B_70),u1_struct_0(A_69))
      | ~ v16_lattices(A_69)
      | ~ v11_lattices(A_69)
      | ~ v10_lattices(A_69)
      | ~ m1_subset_1(B_70,u1_struct_0(A_69))
      | ~ l3_lattices(A_69)
      | v2_struct_0(A_69) ) ),
    inference(resolution,[status(thm)],[c_78,c_14])).

tff(c_250,plain,(
    ! [A_72,B_73] :
      ( k2_lattices(A_72,k7_lattices(A_72,B_73),B_73) = k5_lattices(A_72)
      | ~ v16_lattices(A_72)
      | ~ v11_lattices(A_72)
      | ~ v10_lattices(A_72)
      | ~ m1_subset_1(B_73,u1_struct_0(A_72))
      | ~ l3_lattices(A_72)
      | v2_struct_0(A_72) ) ),
    inference(resolution,[status(thm)],[c_24,c_237])).

tff(c_254,plain,
    ( k2_lattices('#skF_1',k7_lattices('#skF_1','#skF_2'),'#skF_2') = k5_lattices('#skF_1')
    | ~ v16_lattices('#skF_1')
    | ~ v11_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_250])).

tff(c_258,plain,
    ( k2_lattices('#skF_1',k7_lattices('#skF_1','#skF_2'),'#skF_2') = k5_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34,c_43,c_57,c_254])).

tff(c_259,plain,(
    k2_lattices('#skF_1',k7_lattices('#skF_1','#skF_2'),'#skF_2') = k5_lattices('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_258])).

tff(c_68,plain,(
    ! [A_41,B_42,C_43] :
      ( r2_lattices(A_41,B_42,C_43)
      | k2_lattices(A_41,C_43,B_42) != k5_lattices(A_41)
      | k2_lattices(A_41,B_42,C_43) != k5_lattices(A_41)
      | k1_lattices(A_41,C_43,B_42) != k6_lattices(A_41)
      | k1_lattices(A_41,B_42,C_43) != k6_lattices(A_41)
      | ~ m1_subset_1(C_43,u1_struct_0(A_41))
      | ~ m1_subset_1(B_42,u1_struct_0(A_41))
      | ~ l3_lattices(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_208,plain,(
    ! [A_64,B_65,B_66] :
      ( r2_lattices(A_64,B_65,k7_lattices(A_64,B_66))
      | k2_lattices(A_64,k7_lattices(A_64,B_66),B_65) != k5_lattices(A_64)
      | k2_lattices(A_64,B_65,k7_lattices(A_64,B_66)) != k5_lattices(A_64)
      | k1_lattices(A_64,k7_lattices(A_64,B_66),B_65) != k6_lattices(A_64)
      | k1_lattices(A_64,B_65,k7_lattices(A_64,B_66)) != k6_lattices(A_64)
      | ~ m1_subset_1(B_65,u1_struct_0(A_64))
      | ~ m1_subset_1(B_66,u1_struct_0(A_64))
      | ~ l3_lattices(A_64)
      | v2_struct_0(A_64) ) ),
    inference(resolution,[status(thm)],[c_24,c_68])).

tff(c_20,plain,(
    ! [A_9,B_13,C_15] :
      ( k7_lattices(A_9,B_13) = C_15
      | ~ r2_lattices(A_9,C_15,B_13)
      | ~ m1_subset_1(C_15,u1_struct_0(A_9))
      | ~ v16_lattices(A_9)
      | ~ v11_lattices(A_9)
      | ~ v10_lattices(A_9)
      | ~ m1_subset_1(B_13,u1_struct_0(A_9))
      | ~ l3_lattices(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_290,plain,(
    ! [A_78,B_79,B_80] :
      ( k7_lattices(A_78,k7_lattices(A_78,B_79)) = B_80
      | ~ v16_lattices(A_78)
      | ~ v11_lattices(A_78)
      | ~ v10_lattices(A_78)
      | ~ m1_subset_1(k7_lattices(A_78,B_79),u1_struct_0(A_78))
      | k2_lattices(A_78,k7_lattices(A_78,B_79),B_80) != k5_lattices(A_78)
      | k2_lattices(A_78,B_80,k7_lattices(A_78,B_79)) != k5_lattices(A_78)
      | k1_lattices(A_78,k7_lattices(A_78,B_79),B_80) != k6_lattices(A_78)
      | k1_lattices(A_78,B_80,k7_lattices(A_78,B_79)) != k6_lattices(A_78)
      | ~ m1_subset_1(B_80,u1_struct_0(A_78))
      | ~ m1_subset_1(B_79,u1_struct_0(A_78))
      | ~ l3_lattices(A_78)
      | v2_struct_0(A_78) ) ),
    inference(resolution,[status(thm)],[c_208,c_20])).

tff(c_294,plain,(
    ! [A_81,B_82,B_83] :
      ( k7_lattices(A_81,k7_lattices(A_81,B_82)) = B_83
      | ~ v16_lattices(A_81)
      | ~ v11_lattices(A_81)
      | ~ v10_lattices(A_81)
      | k2_lattices(A_81,k7_lattices(A_81,B_82),B_83) != k5_lattices(A_81)
      | k2_lattices(A_81,B_83,k7_lattices(A_81,B_82)) != k5_lattices(A_81)
      | k1_lattices(A_81,k7_lattices(A_81,B_82),B_83) != k6_lattices(A_81)
      | k1_lattices(A_81,B_83,k7_lattices(A_81,B_82)) != k6_lattices(A_81)
      | ~ m1_subset_1(B_83,u1_struct_0(A_81))
      | ~ m1_subset_1(B_82,u1_struct_0(A_81))
      | ~ l3_lattices(A_81)
      | v2_struct_0(A_81) ) ),
    inference(resolution,[status(thm)],[c_24,c_290])).

tff(c_298,plain,
    ( k7_lattices('#skF_1',k7_lattices('#skF_1','#skF_2')) = '#skF_2'
    | ~ v16_lattices('#skF_1')
    | ~ v11_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | k2_lattices('#skF_1','#skF_2',k7_lattices('#skF_1','#skF_2')) != k5_lattices('#skF_1')
    | k1_lattices('#skF_1',k7_lattices('#skF_1','#skF_2'),'#skF_2') != k6_lattices('#skF_1')
    | k1_lattices('#skF_1','#skF_2',k7_lattices('#skF_1','#skF_2')) != k6_lattices('#skF_1')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l3_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_294])).

tff(c_304,plain,
    ( k7_lattices('#skF_1',k7_lattices('#skF_1','#skF_2')) = '#skF_2'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_108,c_207,c_180,c_34,c_43,c_57,c_298])).

tff(c_306,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_26,c_304])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.93/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.70  
% 2.93/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.70  %$ r2_lattices > m1_subset_1 > v2_struct_0 > v17_lattices > v16_lattices > v15_lattices > v11_lattices > v10_lattices > l3_lattices > k2_lattices > k1_lattices > k7_lattices > #nlpp > u1_struct_0 > k6_lattices > k5_lattices > #skF_2 > #skF_1
% 2.93/1.70  
% 2.93/1.70  %Foreground sorts:
% 2.93/1.70  
% 2.93/1.70  
% 2.93/1.70  %Background operators:
% 2.93/1.70  
% 2.93/1.70  
% 2.93/1.70  %Foreground operators:
% 2.93/1.70  tff(l3_lattices, type, l3_lattices: $i > $o).
% 2.93/1.70  tff(k6_lattices, type, k6_lattices: $i > $i).
% 2.93/1.70  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.93/1.70  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 2.93/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.93/1.70  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 2.93/1.70  tff(r2_lattices, type, r2_lattices: ($i * $i * $i) > $o).
% 2.93/1.70  tff(v17_lattices, type, v17_lattices: $i > $o).
% 2.93/1.70  tff('#skF_2', type, '#skF_2': $i).
% 2.93/1.70  tff('#skF_1', type, '#skF_1': $i).
% 2.93/1.70  tff(v10_lattices, type, v10_lattices: $i > $o).
% 2.93/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.93/1.70  tff(v11_lattices, type, v11_lattices: $i > $o).
% 2.93/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.93/1.70  tff(k5_lattices, type, k5_lattices: $i > $i).
% 2.93/1.70  tff(k7_lattices, type, k7_lattices: ($i * $i) > $i).
% 2.93/1.70  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.93/1.70  tff(v16_lattices, type, v16_lattices: $i > $o).
% 2.93/1.70  tff(v15_lattices, type, v15_lattices: $i > $o).
% 2.93/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.93/1.70  
% 2.93/1.72  tff(f_112, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v17_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k7_lattices(A, k7_lattices(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_lattices)).
% 2.93/1.72  tff(f_41, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v17_lattices(A)) => (((~v2_struct_0(A) & v11_lattices(A)) & v15_lattices(A)) & v16_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_lattices)).
% 2.93/1.72  tff(f_97, axiom, (![A, B]: (((~v2_struct_0(A) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k7_lattices(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_lattices)).
% 2.93/1.72  tff(f_88, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (((((~v2_struct_0(A) & v10_lattices(A)) & v11_lattices(A)) & v16_lattices(A)) & l3_lattices(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k7_lattices(A, B)) <=> r2_lattices(A, C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d21_lattices)).
% 2.93/1.72  tff(f_62, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattices(A, B, C) <=> ((((k1_lattices(A, B, C) = k6_lattices(A)) & (k1_lattices(A, C, B) = k6_lattices(A))) & (k2_lattices(A, B, C) = k5_lattices(A))) & (k2_lattices(A, C, B) = k5_lattices(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_lattices)).
% 2.93/1.72  tff(c_36, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.93/1.72  tff(c_26, plain, (k7_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.93/1.72  tff(c_30, plain, (l3_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.93/1.72  tff(c_28, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.93/1.72  tff(c_34, plain, (v10_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.93/1.72  tff(c_32, plain, (v17_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.93/1.72  tff(c_37, plain, (![A_19]: (v11_lattices(A_19) | ~v17_lattices(A_19) | v2_struct_0(A_19) | ~l3_lattices(A_19))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.93/1.72  tff(c_40, plain, (v11_lattices('#skF_1') | ~v17_lattices('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_37, c_36])).
% 2.93/1.72  tff(c_43, plain, (v11_lattices('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_40])).
% 2.93/1.72  tff(c_51, plain, (![A_21]: (v16_lattices(A_21) | ~v17_lattices(A_21) | v2_struct_0(A_21) | ~l3_lattices(A_21))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.93/1.72  tff(c_54, plain, (v16_lattices('#skF_1') | ~v17_lattices('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_51, c_36])).
% 2.93/1.72  tff(c_57, plain, (v16_lattices('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_54])).
% 2.93/1.72  tff(c_24, plain, (![A_16, B_17]: (m1_subset_1(k7_lattices(A_16, B_17), u1_struct_0(A_16)) | ~m1_subset_1(B_17, u1_struct_0(A_16)) | ~l3_lattices(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.93/1.72  tff(c_64, plain, (![A_39, B_40]: (r2_lattices(A_39, k7_lattices(A_39, B_40), B_40) | ~m1_subset_1(k7_lattices(A_39, B_40), u1_struct_0(A_39)) | ~v16_lattices(A_39) | ~v11_lattices(A_39) | ~v10_lattices(A_39) | ~m1_subset_1(B_40, u1_struct_0(A_39)) | ~l3_lattices(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.93/1.72  tff(c_78, plain, (![A_44, B_45]: (r2_lattices(A_44, k7_lattices(A_44, B_45), B_45) | ~v16_lattices(A_44) | ~v11_lattices(A_44) | ~v10_lattices(A_44) | ~m1_subset_1(B_45, u1_struct_0(A_44)) | ~l3_lattices(A_44) | v2_struct_0(A_44))), inference(resolution, [status(thm)], [c_24, c_64])).
% 2.93/1.72  tff(c_16, plain, (![A_2, C_8, B_6]: (k1_lattices(A_2, C_8, B_6)=k6_lattices(A_2) | ~r2_lattices(A_2, B_6, C_8) | ~m1_subset_1(C_8, u1_struct_0(A_2)) | ~m1_subset_1(B_6, u1_struct_0(A_2)) | ~l3_lattices(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.93/1.72  tff(c_95, plain, (![A_46, B_47]: (k1_lattices(A_46, B_47, k7_lattices(A_46, B_47))=k6_lattices(A_46) | ~m1_subset_1(k7_lattices(A_46, B_47), u1_struct_0(A_46)) | ~v16_lattices(A_46) | ~v11_lattices(A_46) | ~v10_lattices(A_46) | ~m1_subset_1(B_47, u1_struct_0(A_46)) | ~l3_lattices(A_46) | v2_struct_0(A_46))), inference(resolution, [status(thm)], [c_78, c_16])).
% 2.93/1.72  tff(c_99, plain, (![A_48, B_49]: (k1_lattices(A_48, B_49, k7_lattices(A_48, B_49))=k6_lattices(A_48) | ~v16_lattices(A_48) | ~v11_lattices(A_48) | ~v10_lattices(A_48) | ~m1_subset_1(B_49, u1_struct_0(A_48)) | ~l3_lattices(A_48) | v2_struct_0(A_48))), inference(resolution, [status(thm)], [c_24, c_95])).
% 2.93/1.72  tff(c_103, plain, (k1_lattices('#skF_1', '#skF_2', k7_lattices('#skF_1', '#skF_2'))=k6_lattices('#skF_1') | ~v16_lattices('#skF_1') | ~v11_lattices('#skF_1') | ~v10_lattices('#skF_1') | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_99])).
% 2.93/1.72  tff(c_107, plain, (k1_lattices('#skF_1', '#skF_2', k7_lattices('#skF_1', '#skF_2'))=k6_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_34, c_43, c_57, c_103])).
% 2.93/1.72  tff(c_108, plain, (k1_lattices('#skF_1', '#skF_2', k7_lattices('#skF_1', '#skF_2'))=k6_lattices('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_36, c_107])).
% 2.93/1.72  tff(c_18, plain, (![A_2, B_6, C_8]: (k1_lattices(A_2, B_6, C_8)=k6_lattices(A_2) | ~r2_lattices(A_2, B_6, C_8) | ~m1_subset_1(C_8, u1_struct_0(A_2)) | ~m1_subset_1(B_6, u1_struct_0(A_2)) | ~l3_lattices(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.93/1.72  tff(c_194, plain, (![A_60, B_61]: (k1_lattices(A_60, k7_lattices(A_60, B_61), B_61)=k6_lattices(A_60) | ~m1_subset_1(k7_lattices(A_60, B_61), u1_struct_0(A_60)) | ~v16_lattices(A_60) | ~v11_lattices(A_60) | ~v10_lattices(A_60) | ~m1_subset_1(B_61, u1_struct_0(A_60)) | ~l3_lattices(A_60) | v2_struct_0(A_60))), inference(resolution, [status(thm)], [c_78, c_18])).
% 2.93/1.72  tff(c_198, plain, (![A_62, B_63]: (k1_lattices(A_62, k7_lattices(A_62, B_63), B_63)=k6_lattices(A_62) | ~v16_lattices(A_62) | ~v11_lattices(A_62) | ~v10_lattices(A_62) | ~m1_subset_1(B_63, u1_struct_0(A_62)) | ~l3_lattices(A_62) | v2_struct_0(A_62))), inference(resolution, [status(thm)], [c_24, c_194])).
% 2.93/1.72  tff(c_202, plain, (k1_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'), '#skF_2')=k6_lattices('#skF_1') | ~v16_lattices('#skF_1') | ~v11_lattices('#skF_1') | ~v10_lattices('#skF_1') | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_198])).
% 2.93/1.72  tff(c_206, plain, (k1_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'), '#skF_2')=k6_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_34, c_43, c_57, c_202])).
% 2.93/1.72  tff(c_207, plain, (k1_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'), '#skF_2')=k6_lattices('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_36, c_206])).
% 2.93/1.72  tff(c_12, plain, (![A_2, C_8, B_6]: (k2_lattices(A_2, C_8, B_6)=k5_lattices(A_2) | ~r2_lattices(A_2, B_6, C_8) | ~m1_subset_1(C_8, u1_struct_0(A_2)) | ~m1_subset_1(B_6, u1_struct_0(A_2)) | ~l3_lattices(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.93/1.72  tff(c_136, plain, (![A_53, B_54]: (k2_lattices(A_53, B_54, k7_lattices(A_53, B_54))=k5_lattices(A_53) | ~m1_subset_1(k7_lattices(A_53, B_54), u1_struct_0(A_53)) | ~v16_lattices(A_53) | ~v11_lattices(A_53) | ~v10_lattices(A_53) | ~m1_subset_1(B_54, u1_struct_0(A_53)) | ~l3_lattices(A_53) | v2_struct_0(A_53))), inference(resolution, [status(thm)], [c_78, c_12])).
% 2.93/1.72  tff(c_171, plain, (![A_56, B_57]: (k2_lattices(A_56, B_57, k7_lattices(A_56, B_57))=k5_lattices(A_56) | ~v16_lattices(A_56) | ~v11_lattices(A_56) | ~v10_lattices(A_56) | ~m1_subset_1(B_57, u1_struct_0(A_56)) | ~l3_lattices(A_56) | v2_struct_0(A_56))), inference(resolution, [status(thm)], [c_24, c_136])).
% 2.93/1.72  tff(c_175, plain, (k2_lattices('#skF_1', '#skF_2', k7_lattices('#skF_1', '#skF_2'))=k5_lattices('#skF_1') | ~v16_lattices('#skF_1') | ~v11_lattices('#skF_1') | ~v10_lattices('#skF_1') | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_171])).
% 2.93/1.72  tff(c_179, plain, (k2_lattices('#skF_1', '#skF_2', k7_lattices('#skF_1', '#skF_2'))=k5_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_34, c_43, c_57, c_175])).
% 2.93/1.72  tff(c_180, plain, (k2_lattices('#skF_1', '#skF_2', k7_lattices('#skF_1', '#skF_2'))=k5_lattices('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_36, c_179])).
% 2.93/1.72  tff(c_14, plain, (![A_2, B_6, C_8]: (k2_lattices(A_2, B_6, C_8)=k5_lattices(A_2) | ~r2_lattices(A_2, B_6, C_8) | ~m1_subset_1(C_8, u1_struct_0(A_2)) | ~m1_subset_1(B_6, u1_struct_0(A_2)) | ~l3_lattices(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.93/1.72  tff(c_237, plain, (![A_69, B_70]: (k2_lattices(A_69, k7_lattices(A_69, B_70), B_70)=k5_lattices(A_69) | ~m1_subset_1(k7_lattices(A_69, B_70), u1_struct_0(A_69)) | ~v16_lattices(A_69) | ~v11_lattices(A_69) | ~v10_lattices(A_69) | ~m1_subset_1(B_70, u1_struct_0(A_69)) | ~l3_lattices(A_69) | v2_struct_0(A_69))), inference(resolution, [status(thm)], [c_78, c_14])).
% 2.93/1.72  tff(c_250, plain, (![A_72, B_73]: (k2_lattices(A_72, k7_lattices(A_72, B_73), B_73)=k5_lattices(A_72) | ~v16_lattices(A_72) | ~v11_lattices(A_72) | ~v10_lattices(A_72) | ~m1_subset_1(B_73, u1_struct_0(A_72)) | ~l3_lattices(A_72) | v2_struct_0(A_72))), inference(resolution, [status(thm)], [c_24, c_237])).
% 2.93/1.72  tff(c_254, plain, (k2_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'), '#skF_2')=k5_lattices('#skF_1') | ~v16_lattices('#skF_1') | ~v11_lattices('#skF_1') | ~v10_lattices('#skF_1') | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_250])).
% 2.93/1.72  tff(c_258, plain, (k2_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'), '#skF_2')=k5_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_34, c_43, c_57, c_254])).
% 2.93/1.72  tff(c_259, plain, (k2_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'), '#skF_2')=k5_lattices('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_36, c_258])).
% 2.93/1.72  tff(c_68, plain, (![A_41, B_42, C_43]: (r2_lattices(A_41, B_42, C_43) | k2_lattices(A_41, C_43, B_42)!=k5_lattices(A_41) | k2_lattices(A_41, B_42, C_43)!=k5_lattices(A_41) | k1_lattices(A_41, C_43, B_42)!=k6_lattices(A_41) | k1_lattices(A_41, B_42, C_43)!=k6_lattices(A_41) | ~m1_subset_1(C_43, u1_struct_0(A_41)) | ~m1_subset_1(B_42, u1_struct_0(A_41)) | ~l3_lattices(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.93/1.72  tff(c_208, plain, (![A_64, B_65, B_66]: (r2_lattices(A_64, B_65, k7_lattices(A_64, B_66)) | k2_lattices(A_64, k7_lattices(A_64, B_66), B_65)!=k5_lattices(A_64) | k2_lattices(A_64, B_65, k7_lattices(A_64, B_66))!=k5_lattices(A_64) | k1_lattices(A_64, k7_lattices(A_64, B_66), B_65)!=k6_lattices(A_64) | k1_lattices(A_64, B_65, k7_lattices(A_64, B_66))!=k6_lattices(A_64) | ~m1_subset_1(B_65, u1_struct_0(A_64)) | ~m1_subset_1(B_66, u1_struct_0(A_64)) | ~l3_lattices(A_64) | v2_struct_0(A_64))), inference(resolution, [status(thm)], [c_24, c_68])).
% 2.93/1.72  tff(c_20, plain, (![A_9, B_13, C_15]: (k7_lattices(A_9, B_13)=C_15 | ~r2_lattices(A_9, C_15, B_13) | ~m1_subset_1(C_15, u1_struct_0(A_9)) | ~v16_lattices(A_9) | ~v11_lattices(A_9) | ~v10_lattices(A_9) | ~m1_subset_1(B_13, u1_struct_0(A_9)) | ~l3_lattices(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.93/1.72  tff(c_290, plain, (![A_78, B_79, B_80]: (k7_lattices(A_78, k7_lattices(A_78, B_79))=B_80 | ~v16_lattices(A_78) | ~v11_lattices(A_78) | ~v10_lattices(A_78) | ~m1_subset_1(k7_lattices(A_78, B_79), u1_struct_0(A_78)) | k2_lattices(A_78, k7_lattices(A_78, B_79), B_80)!=k5_lattices(A_78) | k2_lattices(A_78, B_80, k7_lattices(A_78, B_79))!=k5_lattices(A_78) | k1_lattices(A_78, k7_lattices(A_78, B_79), B_80)!=k6_lattices(A_78) | k1_lattices(A_78, B_80, k7_lattices(A_78, B_79))!=k6_lattices(A_78) | ~m1_subset_1(B_80, u1_struct_0(A_78)) | ~m1_subset_1(B_79, u1_struct_0(A_78)) | ~l3_lattices(A_78) | v2_struct_0(A_78))), inference(resolution, [status(thm)], [c_208, c_20])).
% 2.93/1.72  tff(c_294, plain, (![A_81, B_82, B_83]: (k7_lattices(A_81, k7_lattices(A_81, B_82))=B_83 | ~v16_lattices(A_81) | ~v11_lattices(A_81) | ~v10_lattices(A_81) | k2_lattices(A_81, k7_lattices(A_81, B_82), B_83)!=k5_lattices(A_81) | k2_lattices(A_81, B_83, k7_lattices(A_81, B_82))!=k5_lattices(A_81) | k1_lattices(A_81, k7_lattices(A_81, B_82), B_83)!=k6_lattices(A_81) | k1_lattices(A_81, B_83, k7_lattices(A_81, B_82))!=k6_lattices(A_81) | ~m1_subset_1(B_83, u1_struct_0(A_81)) | ~m1_subset_1(B_82, u1_struct_0(A_81)) | ~l3_lattices(A_81) | v2_struct_0(A_81))), inference(resolution, [status(thm)], [c_24, c_290])).
% 2.93/1.72  tff(c_298, plain, (k7_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'))='#skF_2' | ~v16_lattices('#skF_1') | ~v11_lattices('#skF_1') | ~v10_lattices('#skF_1') | k2_lattices('#skF_1', '#skF_2', k7_lattices('#skF_1', '#skF_2'))!=k5_lattices('#skF_1') | k1_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'), '#skF_2')!=k6_lattices('#skF_1') | k1_lattices('#skF_1', '#skF_2', k7_lattices('#skF_1', '#skF_2'))!=k6_lattices('#skF_1') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_259, c_294])).
% 2.93/1.72  tff(c_304, plain, (k7_lattices('#skF_1', k7_lattices('#skF_1', '#skF_2'))='#skF_2' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_108, c_207, c_180, c_34, c_43, c_57, c_298])).
% 2.93/1.72  tff(c_306, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_26, c_304])).
% 2.93/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.72  
% 2.93/1.72  Inference rules
% 2.93/1.72  ----------------------
% 2.93/1.72  #Ref     : 0
% 2.93/1.72  #Sup     : 58
% 2.93/1.72  #Fact    : 0
% 2.93/1.72  #Define  : 0
% 2.93/1.72  #Split   : 1
% 2.93/1.72  #Chain   : 0
% 2.93/1.72  #Close   : 0
% 2.93/1.72  
% 2.93/1.72  Ordering : KBO
% 2.93/1.72  
% 2.93/1.72  Simplification rules
% 2.93/1.72  ----------------------
% 2.93/1.72  #Subsume      : 7
% 2.93/1.72  #Demod        : 51
% 2.93/1.72  #Tautology    : 27
% 2.93/1.72  #SimpNegUnit  : 14
% 2.93/1.72  #BackRed      : 0
% 2.93/1.72  
% 2.93/1.72  #Partial instantiations: 0
% 2.93/1.72  #Strategies tried      : 1
% 2.93/1.72  
% 2.93/1.72  Timing (in seconds)
% 2.93/1.72  ----------------------
% 2.93/1.72  Preprocessing        : 0.50
% 2.93/1.72  Parsing              : 0.26
% 2.93/1.72  CNF conversion       : 0.03
% 2.93/1.72  Main loop            : 0.32
% 2.93/1.72  Inferencing          : 0.13
% 2.93/1.72  Reduction            : 0.08
% 2.93/1.72  Demodulation         : 0.06
% 2.93/1.72  BG Simplification    : 0.02
% 2.93/1.72  Subsumption          : 0.06
% 2.93/1.73  Abstraction          : 0.02
% 2.93/1.73  MUC search           : 0.00
% 2.93/1.73  Cooper               : 0.00
% 2.93/1.73  Total                : 0.86
% 2.93/1.73  Index Insertion      : 0.00
% 2.93/1.73  Index Deletion       : 0.00
% 2.93/1.73  Index Matching       : 0.00
% 2.93/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
