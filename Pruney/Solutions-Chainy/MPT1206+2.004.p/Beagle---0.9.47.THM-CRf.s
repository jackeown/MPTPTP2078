%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:15 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 298 expanded)
%              Number of leaves         :   34 ( 118 expanded)
%              Depth                    :   14
%              Number of atoms          :  260 ( 981 expanded)
%              Number of equality atoms :   43 ( 138 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > k5_lattices > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(k3_lattices,type,(
    k3_lattices: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k2_lattices,type,(
    k2_lattices: ( $i * $i * $i ) > $i )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_lattices,type,(
    k4_lattices: ( $i * $i * $i ) > $i )).

tff(k1_lattices,type,(
    k1_lattices: ( $i * $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v13_lattices,type,(
    v13_lattices: $i > $o )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_lattices,type,(
    k5_lattices: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_149,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v13_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => k4_lattices(A,k5_lattices(A),B) = k5_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_lattices)).

tff(f_75,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_69,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => m1_subset_1(k5_lattices(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

tff(f_47,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( ( ~ v2_struct_0(A)
          & v10_lattices(A) )
       => ( ~ v2_struct_0(A)
          & v4_lattices(A)
          & v5_lattices(A)
          & v6_lattices(A)
          & v7_lattices(A)
          & v8_lattices(A)
          & v9_lattices(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k2_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

tff(f_120,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_lattices(A,B,C)
              <=> k2_lattices(A,B,C) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).

tff(f_62,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_lattices(A,B,C)
              <=> k1_lattices(A,B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).

tff(f_134,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v13_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k3_lattices(A,k5_lattices(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_lattices)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k1_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_40,plain,(
    l3_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_47,plain,(
    ! [A_28] :
      ( l1_lattices(A_28)
      | ~ l3_lattices(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_51,plain,(
    l1_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_47])).

tff(c_20,plain,(
    ! [A_9] :
      ( m1_subset_1(k5_lattices(A_9),u1_struct_0(A_9))
      | ~ l1_lattices(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_44,plain,(
    v10_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_112,plain,(
    ! [A_47,B_48,C_49] :
      ( k4_lattices(A_47,B_48,C_49) = k2_lattices(A_47,B_48,C_49)
      | ~ m1_subset_1(C_49,u1_struct_0(A_47))
      | ~ m1_subset_1(B_48,u1_struct_0(A_47))
      | ~ l1_lattices(A_47)
      | ~ v6_lattices(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_116,plain,(
    ! [B_48] :
      ( k4_lattices('#skF_1',B_48,'#skF_2') = k2_lattices('#skF_1',B_48,'#skF_2')
      | ~ m1_subset_1(B_48,u1_struct_0('#skF_1'))
      | ~ l1_lattices('#skF_1')
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_112])).

tff(c_120,plain,(
    ! [B_48] :
      ( k4_lattices('#skF_1',B_48,'#skF_2') = k2_lattices('#skF_1',B_48,'#skF_2')
      | ~ m1_subset_1(B_48,u1_struct_0('#skF_1'))
      | ~ v6_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_116])).

tff(c_121,plain,(
    ! [B_48] :
      ( k4_lattices('#skF_1',B_48,'#skF_2') = k2_lattices('#skF_1',B_48,'#skF_2')
      | ~ m1_subset_1(B_48,u1_struct_0('#skF_1'))
      | ~ v6_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_120])).

tff(c_203,plain,(
    ~ v6_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_206,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_203])).

tff(c_209,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44,c_206])).

tff(c_211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_209])).

tff(c_224,plain,(
    ! [B_58] :
      ( k4_lattices('#skF_1',B_58,'#skF_2') = k2_lattices('#skF_1',B_58,'#skF_2')
      | ~ m1_subset_1(B_58,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_228,plain,
    ( k4_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') = k2_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2')
    | ~ l1_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_224])).

tff(c_234,plain,
    ( k4_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') = k2_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_228])).

tff(c_235,plain,(
    k4_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') = k2_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_234])).

tff(c_36,plain,(
    k4_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') != k5_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_241,plain,(
    k2_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') != k5_lattices('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_36])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_270,plain,(
    ! [A_60,B_61,C_62] :
      ( r1_lattices(A_60,B_61,C_62)
      | k2_lattices(A_60,B_61,C_62) != B_61
      | ~ m1_subset_1(C_62,u1_struct_0(A_60))
      | ~ m1_subset_1(B_61,u1_struct_0(A_60))
      | ~ l3_lattices(A_60)
      | ~ v9_lattices(A_60)
      | ~ v8_lattices(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_274,plain,(
    ! [B_61] :
      ( r1_lattices('#skF_1',B_61,'#skF_2')
      | k2_lattices('#skF_1',B_61,'#skF_2') != B_61
      | ~ m1_subset_1(B_61,u1_struct_0('#skF_1'))
      | ~ l3_lattices('#skF_1')
      | ~ v9_lattices('#skF_1')
      | ~ v8_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_270])).

tff(c_278,plain,(
    ! [B_61] :
      ( r1_lattices('#skF_1',B_61,'#skF_2')
      | k2_lattices('#skF_1',B_61,'#skF_2') != B_61
      | ~ m1_subset_1(B_61,u1_struct_0('#skF_1'))
      | ~ v9_lattices('#skF_1')
      | ~ v8_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_274])).

tff(c_279,plain,(
    ! [B_61] :
      ( r1_lattices('#skF_1',B_61,'#skF_2')
      | k2_lattices('#skF_1',B_61,'#skF_2') != B_61
      | ~ m1_subset_1(B_61,u1_struct_0('#skF_1'))
      | ~ v9_lattices('#skF_1')
      | ~ v8_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_278])).

tff(c_284,plain,(
    ~ v8_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_279])).

tff(c_287,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_284])).

tff(c_290,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44,c_287])).

tff(c_292,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_290])).

tff(c_294,plain,(
    v8_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_279])).

tff(c_2,plain,(
    ! [A_1] :
      ( v9_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_293,plain,(
    ! [B_61] :
      ( ~ v9_lattices('#skF_1')
      | r1_lattices('#skF_1',B_61,'#skF_2')
      | k2_lattices('#skF_1',B_61,'#skF_2') != B_61
      | ~ m1_subset_1(B_61,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_279])).

tff(c_295,plain,(
    ~ v9_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_293])).

tff(c_298,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_295])).

tff(c_301,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44,c_298])).

tff(c_303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_301])).

tff(c_305,plain,(
    v9_lattices('#skF_1') ),
    inference(splitRight,[status(thm)],[c_293])).

tff(c_52,plain,(
    ! [A_29] :
      ( l2_lattices(A_29)
      | ~ l3_lattices(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_56,plain,(
    l2_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_52])).

tff(c_88,plain,(
    ! [A_43,B_44,C_45] :
      ( r1_lattices(A_43,B_44,C_45)
      | k1_lattices(A_43,B_44,C_45) != C_45
      | ~ m1_subset_1(C_45,u1_struct_0(A_43))
      | ~ m1_subset_1(B_44,u1_struct_0(A_43))
      | ~ l2_lattices(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_92,plain,(
    ! [B_44] :
      ( r1_lattices('#skF_1',B_44,'#skF_2')
      | k1_lattices('#skF_1',B_44,'#skF_2') != '#skF_2'
      | ~ m1_subset_1(B_44,u1_struct_0('#skF_1'))
      | ~ l2_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_88])).

tff(c_96,plain,(
    ! [B_44] :
      ( r1_lattices('#skF_1',B_44,'#skF_2')
      | k1_lattices('#skF_1',B_44,'#skF_2') != '#skF_2'
      | ~ m1_subset_1(B_44,u1_struct_0('#skF_1'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_92])).

tff(c_98,plain,(
    ! [B_46] :
      ( r1_lattices('#skF_1',B_46,'#skF_2')
      | k1_lattices('#skF_1',B_46,'#skF_2') != '#skF_2'
      | ~ m1_subset_1(B_46,u1_struct_0('#skF_1')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_96])).

tff(c_102,plain,
    ( r1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2')
    | k1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') != '#skF_2'
    | ~ l1_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_98])).

tff(c_108,plain,
    ( r1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2')
    | k1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') != '#skF_2'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_102])).

tff(c_109,plain,
    ( r1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2')
    | k1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_108])).

tff(c_122,plain,(
    k1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_109])).

tff(c_42,plain,(
    v13_lattices('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_64,plain,(
    ! [A_37,B_38] :
      ( k3_lattices(A_37,k5_lattices(A_37),B_38) = B_38
      | ~ m1_subset_1(B_38,u1_struct_0(A_37))
      | ~ l3_lattices(A_37)
      | ~ v13_lattices(A_37)
      | ~ v10_lattices(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_68,plain,
    ( k3_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') = '#skF_2'
    | ~ l3_lattices('#skF_1')
    | ~ v13_lattices('#skF_1')
    | ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_64])).

tff(c_72,plain,
    ( k3_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') = '#skF_2'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_68])).

tff(c_73,plain,(
    k3_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_72])).

tff(c_12,plain,(
    ! [A_1] :
      ( v4_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_156,plain,(
    ! [A_51,B_52,C_53] :
      ( k3_lattices(A_51,B_52,C_53) = k1_lattices(A_51,B_52,C_53)
      | ~ m1_subset_1(C_53,u1_struct_0(A_51))
      | ~ m1_subset_1(B_52,u1_struct_0(A_51))
      | ~ l2_lattices(A_51)
      | ~ v4_lattices(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_160,plain,(
    ! [B_52] :
      ( k3_lattices('#skF_1',B_52,'#skF_2') = k1_lattices('#skF_1',B_52,'#skF_2')
      | ~ m1_subset_1(B_52,u1_struct_0('#skF_1'))
      | ~ l2_lattices('#skF_1')
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_156])).

tff(c_164,plain,(
    ! [B_52] :
      ( k3_lattices('#skF_1',B_52,'#skF_2') = k1_lattices('#skF_1',B_52,'#skF_2')
      | ~ m1_subset_1(B_52,u1_struct_0('#skF_1'))
      | ~ v4_lattices('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_160])).

tff(c_165,plain,(
    ! [B_52] :
      ( k3_lattices('#skF_1',B_52,'#skF_2') = k1_lattices('#skF_1',B_52,'#skF_2')
      | ~ m1_subset_1(B_52,u1_struct_0('#skF_1'))
      | ~ v4_lattices('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_164])).

tff(c_166,plain,(
    ~ v4_lattices('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_165])).

tff(c_169,plain,
    ( ~ v10_lattices('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l3_lattices('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_166])).

tff(c_172,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44,c_169])).

tff(c_174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_172])).

tff(c_177,plain,(
    ! [B_54] :
      ( k3_lattices('#skF_1',B_54,'#skF_2') = k1_lattices('#skF_1',B_54,'#skF_2')
      | ~ m1_subset_1(B_54,u1_struct_0('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_181,plain,
    ( k3_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') = k1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2')
    | ~ l1_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_177])).

tff(c_187,plain,
    ( k1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') = '#skF_2'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_73,c_181])).

tff(c_189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_122,c_187])).

tff(c_190,plain,(
    r1_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_320,plain,(
    ! [A_64,B_65,C_66] :
      ( k2_lattices(A_64,B_65,C_66) = B_65
      | ~ r1_lattices(A_64,B_65,C_66)
      | ~ m1_subset_1(C_66,u1_struct_0(A_64))
      | ~ m1_subset_1(B_65,u1_struct_0(A_64))
      | ~ l3_lattices(A_64)
      | ~ v9_lattices(A_64)
      | ~ v8_lattices(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_322,plain,
    ( k2_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') = k5_lattices('#skF_1')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ m1_subset_1(k5_lattices('#skF_1'),u1_struct_0('#skF_1'))
    | ~ l3_lattices('#skF_1')
    | ~ v9_lattices('#skF_1')
    | ~ v8_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_190,c_320])).

tff(c_325,plain,
    ( k2_lattices('#skF_1',k5_lattices('#skF_1'),'#skF_2') = k5_lattices('#skF_1')
    | ~ m1_subset_1(k5_lattices('#skF_1'),u1_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_305,c_40,c_38,c_322])).

tff(c_326,plain,(
    ~ m1_subset_1(k5_lattices('#skF_1'),u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_241,c_325])).

tff(c_329,plain,
    ( ~ l1_lattices('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_326])).

tff(c_332,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_329])).

tff(c_334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_332])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n003.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 11:10:42 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.35  
% 2.50/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.36  %$ r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > k5_lattices > #skF_2 > #skF_1
% 2.50/1.36  
% 2.50/1.36  %Foreground sorts:
% 2.50/1.36  
% 2.50/1.36  
% 2.50/1.36  %Background operators:
% 2.50/1.36  
% 2.50/1.36  
% 2.50/1.36  %Foreground operators:
% 2.50/1.36  tff(l3_lattices, type, l3_lattices: $i > $o).
% 2.50/1.36  tff(k3_lattices, type, k3_lattices: ($i * $i * $i) > $i).
% 2.50/1.36  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.50/1.36  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 2.50/1.36  tff(l2_lattices, type, l2_lattices: $i > $o).
% 2.50/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.36  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 2.50/1.36  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 2.50/1.36  tff(l1_lattices, type, l1_lattices: $i > $o).
% 2.50/1.36  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 2.50/1.36  tff(v4_lattices, type, v4_lattices: $i > $o).
% 2.50/1.36  tff(v6_lattices, type, v6_lattices: $i > $o).
% 2.50/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.50/1.36  tff(v9_lattices, type, v9_lattices: $i > $o).
% 2.50/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.50/1.36  tff(v5_lattices, type, v5_lattices: $i > $o).
% 2.50/1.36  tff(v10_lattices, type, v10_lattices: $i > $o).
% 2.50/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.36  tff(v13_lattices, type, v13_lattices: $i > $o).
% 2.50/1.36  tff(v8_lattices, type, v8_lattices: $i > $o).
% 2.50/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.36  tff(k5_lattices, type, k5_lattices: $i > $i).
% 2.50/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.50/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.50/1.36  tff(v7_lattices, type, v7_lattices: $i > $o).
% 2.50/1.36  
% 2.50/1.38  tff(f_149, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v13_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k4_lattices(A, k5_lattices(A), B) = k5_lattices(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_lattices)).
% 2.50/1.38  tff(f_75, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 2.50/1.38  tff(f_69, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => m1_subset_1(k5_lattices(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_lattices)).
% 2.50/1.38  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 2.50/1.38  tff(f_101, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k2_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 2.50/1.38  tff(f_120, axiom, (![A]: ((((~v2_struct_0(A) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k2_lattices(A, B, C) = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_lattices)).
% 2.50/1.38  tff(f_62, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k1_lattices(A, B, C) = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_lattices)).
% 2.50/1.38  tff(f_134, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v13_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k3_lattices(A, k5_lattices(A), B) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_lattices)).
% 2.50/1.38  tff(f_88, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 2.50/1.38  tff(c_46, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.50/1.38  tff(c_40, plain, (l3_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.50/1.38  tff(c_47, plain, (![A_28]: (l1_lattices(A_28) | ~l3_lattices(A_28))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.50/1.38  tff(c_51, plain, (l1_lattices('#skF_1')), inference(resolution, [status(thm)], [c_40, c_47])).
% 2.50/1.38  tff(c_20, plain, (![A_9]: (m1_subset_1(k5_lattices(A_9), u1_struct_0(A_9)) | ~l1_lattices(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.50/1.38  tff(c_44, plain, (v10_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.50/1.38  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.50/1.38  tff(c_38, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.50/1.38  tff(c_112, plain, (![A_47, B_48, C_49]: (k4_lattices(A_47, B_48, C_49)=k2_lattices(A_47, B_48, C_49) | ~m1_subset_1(C_49, u1_struct_0(A_47)) | ~m1_subset_1(B_48, u1_struct_0(A_47)) | ~l1_lattices(A_47) | ~v6_lattices(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.50/1.38  tff(c_116, plain, (![B_48]: (k4_lattices('#skF_1', B_48, '#skF_2')=k2_lattices('#skF_1', B_48, '#skF_2') | ~m1_subset_1(B_48, u1_struct_0('#skF_1')) | ~l1_lattices('#skF_1') | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_112])).
% 2.50/1.38  tff(c_120, plain, (![B_48]: (k4_lattices('#skF_1', B_48, '#skF_2')=k2_lattices('#skF_1', B_48, '#skF_2') | ~m1_subset_1(B_48, u1_struct_0('#skF_1')) | ~v6_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_116])).
% 2.50/1.38  tff(c_121, plain, (![B_48]: (k4_lattices('#skF_1', B_48, '#skF_2')=k2_lattices('#skF_1', B_48, '#skF_2') | ~m1_subset_1(B_48, u1_struct_0('#skF_1')) | ~v6_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_46, c_120])).
% 2.50/1.38  tff(c_203, plain, (~v6_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_121])).
% 2.50/1.38  tff(c_206, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_8, c_203])).
% 2.50/1.38  tff(c_209, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44, c_206])).
% 2.50/1.38  tff(c_211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_209])).
% 2.50/1.38  tff(c_224, plain, (![B_58]: (k4_lattices('#skF_1', B_58, '#skF_2')=k2_lattices('#skF_1', B_58, '#skF_2') | ~m1_subset_1(B_58, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_121])).
% 2.50/1.38  tff(c_228, plain, (k4_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')=k2_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2') | ~l1_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_224])).
% 2.50/1.38  tff(c_234, plain, (k4_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')=k2_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_51, c_228])).
% 2.50/1.38  tff(c_235, plain, (k4_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')=k2_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_46, c_234])).
% 2.50/1.38  tff(c_36, plain, (k4_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')!=k5_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.50/1.38  tff(c_241, plain, (k2_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')!=k5_lattices('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_235, c_36])).
% 2.50/1.38  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.50/1.38  tff(c_270, plain, (![A_60, B_61, C_62]: (r1_lattices(A_60, B_61, C_62) | k2_lattices(A_60, B_61, C_62)!=B_61 | ~m1_subset_1(C_62, u1_struct_0(A_60)) | ~m1_subset_1(B_61, u1_struct_0(A_60)) | ~l3_lattices(A_60) | ~v9_lattices(A_60) | ~v8_lattices(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.50/1.38  tff(c_274, plain, (![B_61]: (r1_lattices('#skF_1', B_61, '#skF_2') | k2_lattices('#skF_1', B_61, '#skF_2')!=B_61 | ~m1_subset_1(B_61, u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_270])).
% 2.50/1.38  tff(c_278, plain, (![B_61]: (r1_lattices('#skF_1', B_61, '#skF_2') | k2_lattices('#skF_1', B_61, '#skF_2')!=B_61 | ~m1_subset_1(B_61, u1_struct_0('#skF_1')) | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_274])).
% 2.50/1.38  tff(c_279, plain, (![B_61]: (r1_lattices('#skF_1', B_61, '#skF_2') | k2_lattices('#skF_1', B_61, '#skF_2')!=B_61 | ~m1_subset_1(B_61, u1_struct_0('#skF_1')) | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_46, c_278])).
% 2.50/1.38  tff(c_284, plain, (~v8_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_279])).
% 2.50/1.38  tff(c_287, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_4, c_284])).
% 2.50/1.38  tff(c_290, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44, c_287])).
% 2.50/1.38  tff(c_292, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_290])).
% 2.50/1.38  tff(c_294, plain, (v8_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_279])).
% 2.50/1.38  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.50/1.38  tff(c_293, plain, (![B_61]: (~v9_lattices('#skF_1') | r1_lattices('#skF_1', B_61, '#skF_2') | k2_lattices('#skF_1', B_61, '#skF_2')!=B_61 | ~m1_subset_1(B_61, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_279])).
% 2.50/1.38  tff(c_295, plain, (~v9_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_293])).
% 2.50/1.38  tff(c_298, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_2, c_295])).
% 2.50/1.38  tff(c_301, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44, c_298])).
% 2.50/1.38  tff(c_303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_301])).
% 2.50/1.38  tff(c_305, plain, (v9_lattices('#skF_1')), inference(splitRight, [status(thm)], [c_293])).
% 2.50/1.38  tff(c_52, plain, (![A_29]: (l2_lattices(A_29) | ~l3_lattices(A_29))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.50/1.38  tff(c_56, plain, (l2_lattices('#skF_1')), inference(resolution, [status(thm)], [c_40, c_52])).
% 2.50/1.38  tff(c_88, plain, (![A_43, B_44, C_45]: (r1_lattices(A_43, B_44, C_45) | k1_lattices(A_43, B_44, C_45)!=C_45 | ~m1_subset_1(C_45, u1_struct_0(A_43)) | ~m1_subset_1(B_44, u1_struct_0(A_43)) | ~l2_lattices(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.50/1.38  tff(c_92, plain, (![B_44]: (r1_lattices('#skF_1', B_44, '#skF_2') | k1_lattices('#skF_1', B_44, '#skF_2')!='#skF_2' | ~m1_subset_1(B_44, u1_struct_0('#skF_1')) | ~l2_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_88])).
% 2.50/1.38  tff(c_96, plain, (![B_44]: (r1_lattices('#skF_1', B_44, '#skF_2') | k1_lattices('#skF_1', B_44, '#skF_2')!='#skF_2' | ~m1_subset_1(B_44, u1_struct_0('#skF_1')) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_92])).
% 2.50/1.38  tff(c_98, plain, (![B_46]: (r1_lattices('#skF_1', B_46, '#skF_2') | k1_lattices('#skF_1', B_46, '#skF_2')!='#skF_2' | ~m1_subset_1(B_46, u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_46, c_96])).
% 2.50/1.38  tff(c_102, plain, (r1_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2') | k1_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')!='#skF_2' | ~l1_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_98])).
% 2.50/1.38  tff(c_108, plain, (r1_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2') | k1_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')!='#skF_2' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_51, c_102])).
% 2.50/1.38  tff(c_109, plain, (r1_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2') | k1_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_46, c_108])).
% 2.50/1.38  tff(c_122, plain, (k1_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')!='#skF_2'), inference(splitLeft, [status(thm)], [c_109])).
% 2.50/1.38  tff(c_42, plain, (v13_lattices('#skF_1')), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.50/1.38  tff(c_64, plain, (![A_37, B_38]: (k3_lattices(A_37, k5_lattices(A_37), B_38)=B_38 | ~m1_subset_1(B_38, u1_struct_0(A_37)) | ~l3_lattices(A_37) | ~v13_lattices(A_37) | ~v10_lattices(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.50/1.38  tff(c_68, plain, (k3_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')='#skF_2' | ~l3_lattices('#skF_1') | ~v13_lattices('#skF_1') | ~v10_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_64])).
% 2.50/1.38  tff(c_72, plain, (k3_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')='#skF_2' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_68])).
% 2.50/1.38  tff(c_73, plain, (k3_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_46, c_72])).
% 2.50/1.38  tff(c_12, plain, (![A_1]: (v4_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.50/1.38  tff(c_156, plain, (![A_51, B_52, C_53]: (k3_lattices(A_51, B_52, C_53)=k1_lattices(A_51, B_52, C_53) | ~m1_subset_1(C_53, u1_struct_0(A_51)) | ~m1_subset_1(B_52, u1_struct_0(A_51)) | ~l2_lattices(A_51) | ~v4_lattices(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.50/1.38  tff(c_160, plain, (![B_52]: (k3_lattices('#skF_1', B_52, '#skF_2')=k1_lattices('#skF_1', B_52, '#skF_2') | ~m1_subset_1(B_52, u1_struct_0('#skF_1')) | ~l2_lattices('#skF_1') | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_156])).
% 2.50/1.38  tff(c_164, plain, (![B_52]: (k3_lattices('#skF_1', B_52, '#skF_2')=k1_lattices('#skF_1', B_52, '#skF_2') | ~m1_subset_1(B_52, u1_struct_0('#skF_1')) | ~v4_lattices('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_160])).
% 2.50/1.38  tff(c_165, plain, (![B_52]: (k3_lattices('#skF_1', B_52, '#skF_2')=k1_lattices('#skF_1', B_52, '#skF_2') | ~m1_subset_1(B_52, u1_struct_0('#skF_1')) | ~v4_lattices('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_46, c_164])).
% 2.50/1.38  tff(c_166, plain, (~v4_lattices('#skF_1')), inference(splitLeft, [status(thm)], [c_165])).
% 2.50/1.38  tff(c_169, plain, (~v10_lattices('#skF_1') | v2_struct_0('#skF_1') | ~l3_lattices('#skF_1')), inference(resolution, [status(thm)], [c_12, c_166])).
% 2.50/1.38  tff(c_172, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44, c_169])).
% 2.50/1.38  tff(c_174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_172])).
% 2.50/1.38  tff(c_177, plain, (![B_54]: (k3_lattices('#skF_1', B_54, '#skF_2')=k1_lattices('#skF_1', B_54, '#skF_2') | ~m1_subset_1(B_54, u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_165])).
% 2.50/1.38  tff(c_181, plain, (k3_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')=k1_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2') | ~l1_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_177])).
% 2.50/1.38  tff(c_187, plain, (k1_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')='#skF_2' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_51, c_73, c_181])).
% 2.50/1.38  tff(c_189, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_122, c_187])).
% 2.50/1.38  tff(c_190, plain, (r1_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_109])).
% 2.50/1.38  tff(c_320, plain, (![A_64, B_65, C_66]: (k2_lattices(A_64, B_65, C_66)=B_65 | ~r1_lattices(A_64, B_65, C_66) | ~m1_subset_1(C_66, u1_struct_0(A_64)) | ~m1_subset_1(B_65, u1_struct_0(A_64)) | ~l3_lattices(A_64) | ~v9_lattices(A_64) | ~v8_lattices(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.50/1.38  tff(c_322, plain, (k2_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')=k5_lattices('#skF_1') | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~m1_subset_1(k5_lattices('#skF_1'), u1_struct_0('#skF_1')) | ~l3_lattices('#skF_1') | ~v9_lattices('#skF_1') | ~v8_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_190, c_320])).
% 2.50/1.38  tff(c_325, plain, (k2_lattices('#skF_1', k5_lattices('#skF_1'), '#skF_2')=k5_lattices('#skF_1') | ~m1_subset_1(k5_lattices('#skF_1'), u1_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_294, c_305, c_40, c_38, c_322])).
% 2.50/1.38  tff(c_326, plain, (~m1_subset_1(k5_lattices('#skF_1'), u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_46, c_241, c_325])).
% 2.50/1.38  tff(c_329, plain, (~l1_lattices('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_326])).
% 2.50/1.38  tff(c_332, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_51, c_329])).
% 2.50/1.38  tff(c_334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_332])).
% 2.50/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.38  
% 2.50/1.38  Inference rules
% 2.50/1.38  ----------------------
% 2.50/1.38  #Ref     : 0
% 2.50/1.38  #Sup     : 51
% 2.50/1.38  #Fact    : 0
% 2.50/1.38  #Define  : 0
% 2.50/1.38  #Split   : 9
% 2.50/1.38  #Chain   : 0
% 2.50/1.38  #Close   : 0
% 2.50/1.38  
% 2.50/1.38  Ordering : KBO
% 2.50/1.38  
% 2.50/1.38  Simplification rules
% 2.50/1.38  ----------------------
% 2.50/1.38  #Subsume      : 1
% 2.50/1.38  #Demod        : 40
% 2.50/1.38  #Tautology    : 19
% 2.50/1.38  #SimpNegUnit  : 21
% 2.50/1.38  #BackRed      : 2
% 2.50/1.38  
% 2.50/1.38  #Partial instantiations: 0
% 2.50/1.38  #Strategies tried      : 1
% 2.50/1.38  
% 2.50/1.38  Timing (in seconds)
% 2.50/1.38  ----------------------
% 2.50/1.38  Preprocessing        : 0.30
% 2.50/1.38  Parsing              : 0.16
% 2.50/1.38  CNF conversion       : 0.02
% 2.50/1.38  Main loop            : 0.23
% 2.50/1.38  Inferencing          : 0.09
% 2.50/1.38  Reduction            : 0.07
% 2.50/1.38  Demodulation         : 0.04
% 2.50/1.38  BG Simplification    : 0.02
% 2.50/1.38  Subsumption          : 0.04
% 2.50/1.38  Abstraction          : 0.02
% 2.50/1.38  MUC search           : 0.00
% 2.50/1.38  Cooper               : 0.00
% 2.50/1.38  Total                : 0.58
% 2.50/1.38  Index Insertion      : 0.00
% 2.50/1.38  Index Deletion       : 0.00
% 2.50/1.38  Index Matching       : 0.00
% 2.50/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
