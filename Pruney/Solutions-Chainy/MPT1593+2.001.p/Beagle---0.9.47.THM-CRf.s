%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:19 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 145 expanded)
%              Number of leaves         :   25 (  61 expanded)
%              Depth                    :   11
%              Number of atoms          :  107 ( 266 expanded)
%              Number of equality atoms :   55 (  96 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_partfun1 > m1_subset_1 > v8_relat_2 > v4_relat_2 > v1_relat_2 > v1_orders_2 > l1_orders_2 > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_48,axiom,(
    ! [A] : k2_yellow_1(A) = g1_orders_2(A,k1_yellow_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_yellow_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_2(k1_yellow_1(A))
      & v4_relat_2(k1_yellow_1(A))
      & v8_relat_2(k1_yellow_1(A))
      & v1_partfun1(k1_yellow_1(A),A)
      & m1_subset_1(k1_yellow_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ( v1_orders_2(g1_orders_2(A,B))
        & l1_orders_2(g1_orders_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_orders_2)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_orders_2(A)
       => A = g1_orders_2(u1_struct_0(A),u1_orders_2(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C,D] :
          ( g1_orders_2(A,B) = g1_orders_2(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

tff(f_63,negated_conjecture,(
    ~ ! [A] :
        ( u1_struct_0(k2_yellow_1(A)) = A
        & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(c_12,plain,(
    ! [A_10] : g1_orders_2(A_10,k1_yellow_1(A_10)) = k2_yellow_1(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_22,plain,(
    ! [A_11] : m1_subset_1(k1_yellow_1(A_11),k1_zfmisc_1(k2_zfmisc_1(A_11,A_11))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_189,plain,(
    ! [A_50,B_51] :
      ( l1_orders_2(g1_orders_2(A_50,B_51))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(k2_zfmisc_1(A_50,A_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_192,plain,(
    ! [A_11] : l1_orders_2(g1_orders_2(A_11,k1_yellow_1(A_11))) ),
    inference(resolution,[status(thm)],[c_22,c_189])).

tff(c_194,plain,(
    ! [A_11] : l1_orders_2(k2_yellow_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_192])).

tff(c_214,plain,(
    ! [A_55,B_56] :
      ( v1_orders_2(g1_orders_2(A_55,B_56))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k2_zfmisc_1(A_55,A_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_217,plain,(
    ! [A_11] : v1_orders_2(g1_orders_2(A_11,k1_yellow_1(A_11))) ),
    inference(resolution,[status(thm)],[c_22,c_214])).

tff(c_219,plain,(
    ! [A_11] : v1_orders_2(k2_yellow_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_217])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_orders_2(u1_struct_0(A_1),u1_orders_2(A_1)) = A_1
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_226,plain,(
    ! [D_58,B_59,C_60,A_61] :
      ( D_58 = B_59
      | g1_orders_2(C_60,D_58) != g1_orders_2(A_61,B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(k2_zfmisc_1(A_61,A_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_238,plain,(
    ! [A_10,D_58,C_60] :
      ( k1_yellow_1(A_10) = D_58
      | k2_yellow_1(A_10) != g1_orders_2(C_60,D_58)
      | ~ m1_subset_1(k1_yellow_1(A_10),k1_zfmisc_1(k2_zfmisc_1(A_10,A_10))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_226])).

tff(c_241,plain,(
    ! [A_62,D_63,C_64] :
      ( k1_yellow_1(A_62) = D_63
      | k2_yellow_1(A_62) != g1_orders_2(C_64,D_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_238])).

tff(c_247,plain,(
    ! [A_1,A_62] :
      ( u1_orders_2(A_1) = k1_yellow_1(A_62)
      | k2_yellow_1(A_62) != A_1
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_241])).

tff(c_264,plain,(
    ! [A_62] :
      ( u1_orders_2(k2_yellow_1(A_62)) = k1_yellow_1(A_62)
      | ~ v1_orders_2(k2_yellow_1(A_62))
      | ~ l1_orders_2(k2_yellow_1(A_62)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_247])).

tff(c_269,plain,(
    ! [A_70] : u1_orders_2(k2_yellow_1(A_70)) = k1_yellow_1(A_70) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_219,c_264])).

tff(c_275,plain,(
    ! [A_70] :
      ( g1_orders_2(u1_struct_0(k2_yellow_1(A_70)),k1_yellow_1(A_70)) = k2_yellow_1(A_70)
      | ~ v1_orders_2(k2_yellow_1(A_70))
      | ~ l1_orders_2(k2_yellow_1(A_70)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_2])).

tff(c_281,plain,(
    ! [A_70] : g1_orders_2(u1_struct_0(k2_yellow_1(A_70)),k1_yellow_1(A_70)) = k2_yellow_1(A_70) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_219,c_275])).

tff(c_304,plain,(
    ! [C_72,A_73,D_74,B_75] :
      ( C_72 = A_73
      | g1_orders_2(C_72,D_74) != g1_orders_2(A_73,B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(k2_zfmisc_1(A_73,A_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_316,plain,(
    ! [C_72,A_10,D_74] :
      ( C_72 = A_10
      | k2_yellow_1(A_10) != g1_orders_2(C_72,D_74)
      | ~ m1_subset_1(k1_yellow_1(A_10),k1_zfmisc_1(k2_zfmisc_1(A_10,A_10))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_304])).

tff(c_319,plain,(
    ! [C_76,A_77,D_78] :
      ( C_76 = A_77
      | k2_yellow_1(A_77) != g1_orders_2(C_76,D_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_316])).

tff(c_322,plain,(
    ! [A_70,A_77] :
      ( u1_struct_0(k2_yellow_1(A_70)) = A_77
      | k2_yellow_1(A_77) != k2_yellow_1(A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_319])).

tff(c_336,plain,(
    ! [A_70] : u1_struct_0(k2_yellow_1(A_70)) = A_70 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_322])).

tff(c_40,plain,(
    ! [A_18,B_19] :
      ( l1_orders_2(g1_orders_2(A_18,B_19))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(k2_zfmisc_1(A_18,A_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_43,plain,(
    ! [A_11] : l1_orders_2(g1_orders_2(A_11,k1_yellow_1(A_11))) ),
    inference(resolution,[status(thm)],[c_22,c_40])).

tff(c_45,plain,(
    ! [A_11] : l1_orders_2(k2_yellow_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_43])).

tff(c_46,plain,(
    ! [A_20,B_21] :
      ( v1_orders_2(g1_orders_2(A_20,B_21))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_zfmisc_1(A_20,A_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_49,plain,(
    ! [A_11] : v1_orders_2(g1_orders_2(A_11,k1_yellow_1(A_11))) ),
    inference(resolution,[status(thm)],[c_22,c_46])).

tff(c_51,plain,(
    ! [A_11] : v1_orders_2(k2_yellow_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_49])).

tff(c_89,plain,(
    ! [C_32,A_33,D_34,B_35] :
      ( C_32 = A_33
      | g1_orders_2(C_32,D_34) != g1_orders_2(A_33,B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(k2_zfmisc_1(A_33,A_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_97,plain,(
    ! [C_32,A_10,D_34] :
      ( C_32 = A_10
      | k2_yellow_1(A_10) != g1_orders_2(C_32,D_34)
      | ~ m1_subset_1(k1_yellow_1(A_10),k1_zfmisc_1(k2_zfmisc_1(A_10,A_10))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_89])).

tff(c_100,plain,(
    ! [C_36,A_37,D_38] :
      ( C_36 = A_37
      | k2_yellow_1(A_37) != g1_orders_2(C_36,D_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_97])).

tff(c_103,plain,(
    ! [A_1,A_37] :
      ( u1_struct_0(A_1) = A_37
      | k2_yellow_1(A_37) != A_1
      | ~ v1_orders_2(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_100])).

tff(c_120,plain,(
    ! [A_37] :
      ( u1_struct_0(k2_yellow_1(A_37)) = A_37
      | ~ v1_orders_2(k2_yellow_1(A_37))
      | ~ l1_orders_2(k2_yellow_1(A_37)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_103])).

tff(c_124,plain,(
    ! [A_45] : u1_struct_0(k2_yellow_1(A_45)) = A_45 ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_51,c_120])).

tff(c_130,plain,(
    ! [A_45] :
      ( g1_orders_2(A_45,u1_orders_2(k2_yellow_1(A_45))) = k2_yellow_1(A_45)
      | ~ v1_orders_2(k2_yellow_1(A_45))
      | ~ l1_orders_2(k2_yellow_1(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_2])).

tff(c_138,plain,(
    ! [A_46] : g1_orders_2(A_46,u1_orders_2(k2_yellow_1(A_46))) = k2_yellow_1(A_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_51,c_130])).

tff(c_67,plain,(
    ! [D_25,B_26,C_27,A_28] :
      ( D_25 = B_26
      | g1_orders_2(C_27,D_25) != g1_orders_2(A_28,B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_75,plain,(
    ! [A_10,D_25,C_27] :
      ( k1_yellow_1(A_10) = D_25
      | k2_yellow_1(A_10) != g1_orders_2(C_27,D_25)
      | ~ m1_subset_1(k1_yellow_1(A_10),k1_zfmisc_1(k2_zfmisc_1(A_10,A_10))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_67])).

tff(c_77,plain,(
    ! [A_10,D_25,C_27] :
      ( k1_yellow_1(A_10) = D_25
      | k2_yellow_1(A_10) != g1_orders_2(C_27,D_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_75])).

tff(c_151,plain,(
    ! [A_46,A_10] :
      ( u1_orders_2(k2_yellow_1(A_46)) = k1_yellow_1(A_10)
      | k2_yellow_1(A_46) != k2_yellow_1(A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_77])).

tff(c_163,plain,(
    ! [A_10] : u1_orders_2(k2_yellow_1(A_10)) = k1_yellow_1(A_10) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_151])).

tff(c_24,plain,
    ( u1_struct_0(k2_yellow_1('#skF_2')) != '#skF_2'
    | u1_orders_2(k2_yellow_1('#skF_1')) != k1_yellow_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_39,plain,(
    u1_orders_2(k2_yellow_1('#skF_1')) != k1_yellow_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_170,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_39])).

tff(c_171,plain,(
    u1_struct_0(k2_yellow_1('#skF_2')) != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_171])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:03:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.26  
% 2.13/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.26  %$ v1_partfun1 > m1_subset_1 > v8_relat_2 > v4_relat_2 > v1_relat_2 > v1_orders_2 > l1_orders_2 > k2_zfmisc_1 > g1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > #skF_2 > #skF_1
% 2.13/1.26  
% 2.13/1.26  %Foreground sorts:
% 2.13/1.26  
% 2.13/1.26  
% 2.13/1.26  %Background operators:
% 2.13/1.26  
% 2.13/1.26  
% 2.13/1.26  %Foreground operators:
% 2.13/1.26  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.13/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.26  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.13/1.26  tff(v1_relat_2, type, v1_relat_2: $i > $o).
% 2.13/1.26  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 2.13/1.26  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 2.13/1.26  tff(v4_relat_2, type, v4_relat_2: $i > $o).
% 2.13/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.26  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.13/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.13/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.13/1.26  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.13/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.13/1.26  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.13/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.26  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.13/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.13/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.13/1.26  
% 2.13/1.27  tff(f_48, axiom, (![A]: (k2_yellow_1(A) = g1_orders_2(A, k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_yellow_1)).
% 2.13/1.27  tff(f_58, axiom, (![A]: ((((v1_relat_2(k1_yellow_1(A)) & v4_relat_2(k1_yellow_1(A))) & v8_relat_2(k1_yellow_1(A))) & v1_partfun1(k1_yellow_1(A), A)) & m1_subset_1(k1_yellow_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_yellow_1)).
% 2.13/1.27  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (v1_orders_2(g1_orders_2(A, B)) & l1_orders_2(g1_orders_2(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_g1_orders_2)).
% 2.13/1.27  tff(f_31, axiom, (![A]: (l1_orders_2(A) => (v1_orders_2(A) => (A = g1_orders_2(u1_struct_0(A), u1_orders_2(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_orders_2)).
% 2.13/1.27  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C, D]: ((g1_orders_2(A, B) = g1_orders_2(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_orders_2)).
% 2.13/1.28  tff(f_63, negated_conjecture, ~(![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 2.13/1.28  tff(c_12, plain, (![A_10]: (g1_orders_2(A_10, k1_yellow_1(A_10))=k2_yellow_1(A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.13/1.28  tff(c_22, plain, (![A_11]: (m1_subset_1(k1_yellow_1(A_11), k1_zfmisc_1(k2_zfmisc_1(A_11, A_11))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.13/1.28  tff(c_189, plain, (![A_50, B_51]: (l1_orders_2(g1_orders_2(A_50, B_51)) | ~m1_subset_1(B_51, k1_zfmisc_1(k2_zfmisc_1(A_50, A_50))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.13/1.28  tff(c_192, plain, (![A_11]: (l1_orders_2(g1_orders_2(A_11, k1_yellow_1(A_11))))), inference(resolution, [status(thm)], [c_22, c_189])).
% 2.13/1.28  tff(c_194, plain, (![A_11]: (l1_orders_2(k2_yellow_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_192])).
% 2.13/1.28  tff(c_214, plain, (![A_55, B_56]: (v1_orders_2(g1_orders_2(A_55, B_56)) | ~m1_subset_1(B_56, k1_zfmisc_1(k2_zfmisc_1(A_55, A_55))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.13/1.28  tff(c_217, plain, (![A_11]: (v1_orders_2(g1_orders_2(A_11, k1_yellow_1(A_11))))), inference(resolution, [status(thm)], [c_22, c_214])).
% 2.13/1.28  tff(c_219, plain, (![A_11]: (v1_orders_2(k2_yellow_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_217])).
% 2.13/1.28  tff(c_2, plain, (![A_1]: (g1_orders_2(u1_struct_0(A_1), u1_orders_2(A_1))=A_1 | ~v1_orders_2(A_1) | ~l1_orders_2(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.13/1.28  tff(c_226, plain, (![D_58, B_59, C_60, A_61]: (D_58=B_59 | g1_orders_2(C_60, D_58)!=g1_orders_2(A_61, B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(k2_zfmisc_1(A_61, A_61))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.13/1.28  tff(c_238, plain, (![A_10, D_58, C_60]: (k1_yellow_1(A_10)=D_58 | k2_yellow_1(A_10)!=g1_orders_2(C_60, D_58) | ~m1_subset_1(k1_yellow_1(A_10), k1_zfmisc_1(k2_zfmisc_1(A_10, A_10))))), inference(superposition, [status(thm), theory('equality')], [c_12, c_226])).
% 2.13/1.28  tff(c_241, plain, (![A_62, D_63, C_64]: (k1_yellow_1(A_62)=D_63 | k2_yellow_1(A_62)!=g1_orders_2(C_64, D_63))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_238])).
% 2.13/1.28  tff(c_247, plain, (![A_1, A_62]: (u1_orders_2(A_1)=k1_yellow_1(A_62) | k2_yellow_1(A_62)!=A_1 | ~v1_orders_2(A_1) | ~l1_orders_2(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_241])).
% 2.13/1.28  tff(c_264, plain, (![A_62]: (u1_orders_2(k2_yellow_1(A_62))=k1_yellow_1(A_62) | ~v1_orders_2(k2_yellow_1(A_62)) | ~l1_orders_2(k2_yellow_1(A_62)))), inference(reflexivity, [status(thm), theory('equality')], [c_247])).
% 2.13/1.28  tff(c_269, plain, (![A_70]: (u1_orders_2(k2_yellow_1(A_70))=k1_yellow_1(A_70))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_219, c_264])).
% 2.13/1.28  tff(c_275, plain, (![A_70]: (g1_orders_2(u1_struct_0(k2_yellow_1(A_70)), k1_yellow_1(A_70))=k2_yellow_1(A_70) | ~v1_orders_2(k2_yellow_1(A_70)) | ~l1_orders_2(k2_yellow_1(A_70)))), inference(superposition, [status(thm), theory('equality')], [c_269, c_2])).
% 2.13/1.28  tff(c_281, plain, (![A_70]: (g1_orders_2(u1_struct_0(k2_yellow_1(A_70)), k1_yellow_1(A_70))=k2_yellow_1(A_70))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_219, c_275])).
% 2.13/1.28  tff(c_304, plain, (![C_72, A_73, D_74, B_75]: (C_72=A_73 | g1_orders_2(C_72, D_74)!=g1_orders_2(A_73, B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(k2_zfmisc_1(A_73, A_73))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.13/1.28  tff(c_316, plain, (![C_72, A_10, D_74]: (C_72=A_10 | k2_yellow_1(A_10)!=g1_orders_2(C_72, D_74) | ~m1_subset_1(k1_yellow_1(A_10), k1_zfmisc_1(k2_zfmisc_1(A_10, A_10))))), inference(superposition, [status(thm), theory('equality')], [c_12, c_304])).
% 2.13/1.28  tff(c_319, plain, (![C_76, A_77, D_78]: (C_76=A_77 | k2_yellow_1(A_77)!=g1_orders_2(C_76, D_78))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_316])).
% 2.13/1.28  tff(c_322, plain, (![A_70, A_77]: (u1_struct_0(k2_yellow_1(A_70))=A_77 | k2_yellow_1(A_77)!=k2_yellow_1(A_70))), inference(superposition, [status(thm), theory('equality')], [c_281, c_319])).
% 2.13/1.28  tff(c_336, plain, (![A_70]: (u1_struct_0(k2_yellow_1(A_70))=A_70)), inference(reflexivity, [status(thm), theory('equality')], [c_322])).
% 2.13/1.28  tff(c_40, plain, (![A_18, B_19]: (l1_orders_2(g1_orders_2(A_18, B_19)) | ~m1_subset_1(B_19, k1_zfmisc_1(k2_zfmisc_1(A_18, A_18))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.13/1.28  tff(c_43, plain, (![A_11]: (l1_orders_2(g1_orders_2(A_11, k1_yellow_1(A_11))))), inference(resolution, [status(thm)], [c_22, c_40])).
% 2.13/1.28  tff(c_45, plain, (![A_11]: (l1_orders_2(k2_yellow_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_43])).
% 2.13/1.28  tff(c_46, plain, (![A_20, B_21]: (v1_orders_2(g1_orders_2(A_20, B_21)) | ~m1_subset_1(B_21, k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.13/1.28  tff(c_49, plain, (![A_11]: (v1_orders_2(g1_orders_2(A_11, k1_yellow_1(A_11))))), inference(resolution, [status(thm)], [c_22, c_46])).
% 2.13/1.28  tff(c_51, plain, (![A_11]: (v1_orders_2(k2_yellow_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_49])).
% 2.13/1.28  tff(c_89, plain, (![C_32, A_33, D_34, B_35]: (C_32=A_33 | g1_orders_2(C_32, D_34)!=g1_orders_2(A_33, B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.13/1.28  tff(c_97, plain, (![C_32, A_10, D_34]: (C_32=A_10 | k2_yellow_1(A_10)!=g1_orders_2(C_32, D_34) | ~m1_subset_1(k1_yellow_1(A_10), k1_zfmisc_1(k2_zfmisc_1(A_10, A_10))))), inference(superposition, [status(thm), theory('equality')], [c_12, c_89])).
% 2.13/1.28  tff(c_100, plain, (![C_36, A_37, D_38]: (C_36=A_37 | k2_yellow_1(A_37)!=g1_orders_2(C_36, D_38))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_97])).
% 2.13/1.28  tff(c_103, plain, (![A_1, A_37]: (u1_struct_0(A_1)=A_37 | k2_yellow_1(A_37)!=A_1 | ~v1_orders_2(A_1) | ~l1_orders_2(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_100])).
% 2.13/1.28  tff(c_120, plain, (![A_37]: (u1_struct_0(k2_yellow_1(A_37))=A_37 | ~v1_orders_2(k2_yellow_1(A_37)) | ~l1_orders_2(k2_yellow_1(A_37)))), inference(reflexivity, [status(thm), theory('equality')], [c_103])).
% 2.13/1.28  tff(c_124, plain, (![A_45]: (u1_struct_0(k2_yellow_1(A_45))=A_45)), inference(demodulation, [status(thm), theory('equality')], [c_45, c_51, c_120])).
% 2.13/1.28  tff(c_130, plain, (![A_45]: (g1_orders_2(A_45, u1_orders_2(k2_yellow_1(A_45)))=k2_yellow_1(A_45) | ~v1_orders_2(k2_yellow_1(A_45)) | ~l1_orders_2(k2_yellow_1(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_124, c_2])).
% 2.13/1.28  tff(c_138, plain, (![A_46]: (g1_orders_2(A_46, u1_orders_2(k2_yellow_1(A_46)))=k2_yellow_1(A_46))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_51, c_130])).
% 2.13/1.28  tff(c_67, plain, (![D_25, B_26, C_27, A_28]: (D_25=B_26 | g1_orders_2(C_27, D_25)!=g1_orders_2(A_28, B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.13/1.28  tff(c_75, plain, (![A_10, D_25, C_27]: (k1_yellow_1(A_10)=D_25 | k2_yellow_1(A_10)!=g1_orders_2(C_27, D_25) | ~m1_subset_1(k1_yellow_1(A_10), k1_zfmisc_1(k2_zfmisc_1(A_10, A_10))))), inference(superposition, [status(thm), theory('equality')], [c_12, c_67])).
% 2.13/1.28  tff(c_77, plain, (![A_10, D_25, C_27]: (k1_yellow_1(A_10)=D_25 | k2_yellow_1(A_10)!=g1_orders_2(C_27, D_25))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_75])).
% 2.13/1.28  tff(c_151, plain, (![A_46, A_10]: (u1_orders_2(k2_yellow_1(A_46))=k1_yellow_1(A_10) | k2_yellow_1(A_46)!=k2_yellow_1(A_10))), inference(superposition, [status(thm), theory('equality')], [c_138, c_77])).
% 2.13/1.28  tff(c_163, plain, (![A_10]: (u1_orders_2(k2_yellow_1(A_10))=k1_yellow_1(A_10))), inference(reflexivity, [status(thm), theory('equality')], [c_151])).
% 2.13/1.28  tff(c_24, plain, (u1_struct_0(k2_yellow_1('#skF_2'))!='#skF_2' | u1_orders_2(k2_yellow_1('#skF_1'))!=k1_yellow_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.13/1.28  tff(c_39, plain, (u1_orders_2(k2_yellow_1('#skF_1'))!=k1_yellow_1('#skF_1')), inference(splitLeft, [status(thm)], [c_24])).
% 2.13/1.28  tff(c_170, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_163, c_39])).
% 2.13/1.28  tff(c_171, plain, (u1_struct_0(k2_yellow_1('#skF_2'))!='#skF_2'), inference(splitRight, [status(thm)], [c_24])).
% 2.13/1.28  tff(c_343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_336, c_171])).
% 2.13/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.28  
% 2.13/1.28  Inference rules
% 2.13/1.28  ----------------------
% 2.13/1.28  #Ref     : 13
% 2.13/1.28  #Sup     : 65
% 2.13/1.28  #Fact    : 0
% 2.13/1.28  #Define  : 0
% 2.13/1.28  #Split   : 2
% 2.13/1.28  #Chain   : 0
% 2.13/1.28  #Close   : 0
% 2.13/1.28  
% 2.13/1.28  Ordering : KBO
% 2.13/1.28  
% 2.13/1.28  Simplification rules
% 2.13/1.28  ----------------------
% 2.13/1.28  #Subsume      : 9
% 2.13/1.28  #Demod        : 30
% 2.13/1.28  #Tautology    : 32
% 2.13/1.28  #SimpNegUnit  : 0
% 2.13/1.28  #BackRed      : 7
% 2.13/1.28  
% 2.13/1.28  #Partial instantiations: 0
% 2.13/1.28  #Strategies tried      : 1
% 2.13/1.28  
% 2.13/1.28  Timing (in seconds)
% 2.13/1.28  ----------------------
% 2.13/1.28  Preprocessing        : 0.27
% 2.13/1.28  Parsing              : 0.15
% 2.13/1.28  CNF conversion       : 0.02
% 2.13/1.28  Main loop            : 0.23
% 2.13/1.28  Inferencing          : 0.09
% 2.13/1.28  Reduction            : 0.06
% 2.13/1.28  Demodulation         : 0.05
% 2.13/1.28  BG Simplification    : 0.01
% 2.13/1.28  Subsumption          : 0.04
% 2.13/1.28  Abstraction          : 0.01
% 2.13/1.28  MUC search           : 0.00
% 2.13/1.28  Cooper               : 0.00
% 2.13/1.28  Total                : 0.54
% 2.13/1.28  Index Insertion      : 0.00
% 2.13/1.28  Index Deletion       : 0.00
% 2.13/1.28  Index Matching       : 0.00
% 2.13/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
