%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1575+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:06 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   59 (  71 expanded)
%              Number of leaves         :   29 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :  123 ( 174 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r2_yellow_0 > r1_yellow_0 > r1_tarski > m1_subset_1 > v3_lattice3 > v2_struct_0 > l1_orders_2 > k3_xboole_0 > k1_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_4 > #skF_3 > #skF_5 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(v3_lattice3,type,(
    v3_lattice3: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_orders_2(A) )
       => ( ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
             => r1_yellow_0(A,B) )
         => v3_lattice3(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_yellow_0)).

tff(f_26,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( r1_yellow_0(A,B)
           => r1_yellow_0(A,k3_xboole_0(B,u1_struct_0(A))) )
          & ( r1_yellow_0(A,k3_xboole_0(B,u1_struct_0(A)))
           => r1_yellow_0(A,B) )
          & ( r2_yellow_0(A,B)
           => r2_yellow_0(A,k3_xboole_0(B,u1_struct_0(A))) )
          & ( r2_yellow_0(A,k3_xboole_0(B,u1_struct_0(A)))
           => r2_yellow_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_yellow_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k1_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_yellow_0(A,B)
           => ( C = k1_yellow_0(A,B)
            <=> ( r2_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r2_lattice3(A,B,D)
                     => r1_orders_2(A,C,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v3_lattice3(A)
      <=> ! [B] :
          ? [C] :
            ( m1_subset_1(C,u1_struct_0(A))
            & r2_lattice3(A,B,C)
            & ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_lattice3(A,B,D)
                 => r1_orders_2(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_lattice3)).

tff(c_42,plain,(
    ~ v3_lattice3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_46,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_50,plain,(
    ! [B_54,A_55] : k3_xboole_0(B_54,A_55) = k3_xboole_0(A_55,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_28,plain,(
    ! [A_43,B_44] : r1_tarski(k3_xboole_0(A_43,B_44),A_43) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_65,plain,(
    ! [B_54,A_55] : r1_tarski(k3_xboole_0(B_54,A_55),A_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_28])).

tff(c_32,plain,(
    ! [A_45,B_46] :
      ( m1_subset_1(A_45,k1_zfmisc_1(B_46))
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_105,plain,(
    ! [B_62] :
      ( r1_yellow_0('#skF_5',B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_111,plain,(
    ! [A_63] :
      ( r1_yellow_0('#skF_5',A_63)
      | ~ r1_tarski(A_63,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_32,c_105])).

tff(c_120,plain,(
    ! [B_54] : r1_yellow_0('#skF_5',k3_xboole_0(B_54,u1_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_65,c_111])).

tff(c_169,plain,(
    ! [A_76,B_77] :
      ( r1_yellow_0(A_76,B_77)
      | ~ r1_yellow_0(A_76,k3_xboole_0(B_77,u1_struct_0(A_76)))
      | ~ l1_orders_2(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_176,plain,(
    ! [B_54] :
      ( r1_yellow_0('#skF_5',B_54)
      | ~ l1_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_120,c_169])).

tff(c_191,plain,(
    ! [B_54] :
      ( r1_yellow_0('#skF_5',B_54)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_176])).

tff(c_192,plain,(
    ! [B_54] : r1_yellow_0('#skF_5',B_54) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_191])).

tff(c_26,plain,(
    ! [A_41,B_42] :
      ( m1_subset_1(k1_yellow_0(A_41,B_42),u1_struct_0(A_41))
      | ~ l1_orders_2(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_234,plain,(
    ! [A_83,B_84] :
      ( r2_lattice3(A_83,B_84,k1_yellow_0(A_83,B_84))
      | ~ r1_yellow_0(A_83,B_84)
      | ~ m1_subset_1(k1_yellow_0(A_83,B_84),u1_struct_0(A_83))
      | ~ l1_orders_2(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_237,plain,(
    ! [A_41,B_42] :
      ( r2_lattice3(A_41,B_42,k1_yellow_0(A_41,B_42))
      | ~ r1_yellow_0(A_41,B_42)
      | ~ l1_orders_2(A_41) ) ),
    inference(resolution,[status(thm)],[c_26,c_234])).

tff(c_8,plain,(
    ! [A_3,C_27] :
      ( m1_subset_1('#skF_3'(A_3,C_27),u1_struct_0(A_3))
      | v3_lattice3(A_3)
      | ~ r2_lattice3(A_3,'#skF_2'(A_3),C_27)
      | ~ m1_subset_1(C_27,u1_struct_0(A_3))
      | ~ l1_orders_2(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_3,C_27] :
      ( r2_lattice3(A_3,'#skF_2'(A_3),'#skF_3'(A_3,C_27))
      | v3_lattice3(A_3)
      | ~ r2_lattice3(A_3,'#skF_2'(A_3),C_27)
      | ~ m1_subset_1(C_27,u1_struct_0(A_3))
      | ~ l1_orders_2(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_313,plain,(
    ! [A_111,B_112,D_113] :
      ( r1_orders_2(A_111,k1_yellow_0(A_111,B_112),D_113)
      | ~ r2_lattice3(A_111,B_112,D_113)
      | ~ m1_subset_1(D_113,u1_struct_0(A_111))
      | ~ r1_yellow_0(A_111,B_112)
      | ~ m1_subset_1(k1_yellow_0(A_111,B_112),u1_struct_0(A_111))
      | ~ l1_orders_2(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_317,plain,(
    ! [A_114,B_115,D_116] :
      ( r1_orders_2(A_114,k1_yellow_0(A_114,B_115),D_116)
      | ~ r2_lattice3(A_114,B_115,D_116)
      | ~ m1_subset_1(D_116,u1_struct_0(A_114))
      | ~ r1_yellow_0(A_114,B_115)
      | ~ l1_orders_2(A_114) ) ),
    inference(resolution,[status(thm)],[c_26,c_313])).

tff(c_4,plain,(
    ! [A_3,C_27] :
      ( ~ r1_orders_2(A_3,C_27,'#skF_3'(A_3,C_27))
      | v3_lattice3(A_3)
      | ~ r2_lattice3(A_3,'#skF_2'(A_3),C_27)
      | ~ m1_subset_1(C_27,u1_struct_0(A_3))
      | ~ l1_orders_2(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_327,plain,(
    ! [A_117,B_118] :
      ( v3_lattice3(A_117)
      | ~ r2_lattice3(A_117,'#skF_2'(A_117),k1_yellow_0(A_117,B_118))
      | ~ m1_subset_1(k1_yellow_0(A_117,B_118),u1_struct_0(A_117))
      | ~ r2_lattice3(A_117,B_118,'#skF_3'(A_117,k1_yellow_0(A_117,B_118)))
      | ~ m1_subset_1('#skF_3'(A_117,k1_yellow_0(A_117,B_118)),u1_struct_0(A_117))
      | ~ r1_yellow_0(A_117,B_118)
      | ~ l1_orders_2(A_117) ) ),
    inference(resolution,[status(thm)],[c_317,c_4])).

tff(c_332,plain,(
    ! [A_119] :
      ( ~ m1_subset_1('#skF_3'(A_119,k1_yellow_0(A_119,'#skF_2'(A_119))),u1_struct_0(A_119))
      | ~ r1_yellow_0(A_119,'#skF_2'(A_119))
      | v3_lattice3(A_119)
      | ~ r2_lattice3(A_119,'#skF_2'(A_119),k1_yellow_0(A_119,'#skF_2'(A_119)))
      | ~ m1_subset_1(k1_yellow_0(A_119,'#skF_2'(A_119)),u1_struct_0(A_119))
      | ~ l1_orders_2(A_119) ) ),
    inference(resolution,[status(thm)],[c_6,c_327])).

tff(c_343,plain,(
    ! [A_123] :
      ( ~ r1_yellow_0(A_123,'#skF_2'(A_123))
      | v3_lattice3(A_123)
      | ~ r2_lattice3(A_123,'#skF_2'(A_123),k1_yellow_0(A_123,'#skF_2'(A_123)))
      | ~ m1_subset_1(k1_yellow_0(A_123,'#skF_2'(A_123)),u1_struct_0(A_123))
      | ~ l1_orders_2(A_123) ) ),
    inference(resolution,[status(thm)],[c_8,c_332])).

tff(c_349,plain,(
    ! [A_124] :
      ( v3_lattice3(A_124)
      | ~ m1_subset_1(k1_yellow_0(A_124,'#skF_2'(A_124)),u1_struct_0(A_124))
      | ~ r1_yellow_0(A_124,'#skF_2'(A_124))
      | ~ l1_orders_2(A_124) ) ),
    inference(resolution,[status(thm)],[c_237,c_343])).

tff(c_355,plain,(
    ! [A_125] :
      ( v3_lattice3(A_125)
      | ~ r1_yellow_0(A_125,'#skF_2'(A_125))
      | ~ l1_orders_2(A_125) ) ),
    inference(resolution,[status(thm)],[c_26,c_349])).

tff(c_359,plain,
    ( v3_lattice3('#skF_5')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_192,c_355])).

tff(c_362,plain,(
    v3_lattice3('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_359])).

tff(c_364,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_362])).

%------------------------------------------------------------------------------
