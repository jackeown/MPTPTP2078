%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:13 EST 2020

% Result     : Theorem 9.62s
% Output     : CNFRefutation 9.62s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 330 expanded)
%              Number of leaves         :   33 ( 141 expanded)
%              Depth                    :   14
%              Number of atoms          :  203 (1449 expanded)
%              Number of equality atoms :   29 (  69 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v2_struct_0 > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > #skF_7 > #skF_5 > #skF_2 > #skF_4 > #skF_11 > #skF_1 > #skF_10 > #skF_9 > #skF_8 > #skF_3 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff(k2_lattices,type,(
    k2_lattices: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_lattices,type,(
    k1_lattices: ( $i * $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_134,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v7_lattices(A)
          & v8_lattices(A)
          & v9_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r1_lattices(A,B,C)
                     => r1_lattices(A,k2_lattices(A,B,D),k2_lattices(A,C,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_lattices)).

tff(f_90,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k2_lattices(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_lattices)).

tff(f_109,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).

tff(f_43,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => ( v7_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => k2_lattices(A,B,k2_lattices(A,C,D)) = k2_lattices(A,k2_lattices(A,B,C),D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_lattices)).

tff(f_58,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( v8_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k1_lattices(A,k2_lattices(A,B,C),C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattices)).

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( v9_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k2_lattices(A,B,k1_lattices(A,B,C)) = B ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattices)).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_48,plain,(
    l3_lattices('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_62,plain,(
    ! [A_72] :
      ( l1_lattices(A_72)
      | ~ l3_lattices(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_66,plain,(
    l1_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_62])).

tff(c_44,plain,(
    m1_subset_1('#skF_10',u1_struct_0('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_42,plain,(
    m1_subset_1('#skF_11',u1_struct_0('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_52,plain,(
    v8_lattices('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_50,plain,(
    v9_lattices('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_28,plain,(
    ! [A_49,B_50,C_51] :
      ( m1_subset_1(k2_lattices(A_49,B_50,C_51),u1_struct_0(A_49))
      | ~ m1_subset_1(C_51,u1_struct_0(A_49))
      | ~ m1_subset_1(B_50,u1_struct_0(A_49))
      | ~ l1_lattices(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_46,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_40,plain,(
    r1_lattices('#skF_8','#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_664,plain,(
    ! [A_99,B_100,C_101] :
      ( k2_lattices(A_99,B_100,C_101) = B_100
      | ~ r1_lattices(A_99,B_100,C_101)
      | ~ m1_subset_1(C_101,u1_struct_0(A_99))
      | ~ m1_subset_1(B_100,u1_struct_0(A_99))
      | ~ l3_lattices(A_99)
      | ~ v9_lattices(A_99)
      | ~ v8_lattices(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_666,plain,
    ( k2_lattices('#skF_8','#skF_9','#skF_10') = '#skF_9'
    | ~ m1_subset_1('#skF_10',u1_struct_0('#skF_8'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_8'))
    | ~ l3_lattices('#skF_8')
    | ~ v9_lattices('#skF_8')
    | ~ v8_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_40,c_664])).

tff(c_669,plain,
    ( k2_lattices('#skF_8','#skF_9','#skF_10') = '#skF_9'
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_44,c_666])).

tff(c_670,plain,(
    k2_lattices('#skF_8','#skF_9','#skF_10') = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_669])).

tff(c_54,plain,(
    v7_lattices('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_944,plain,(
    ! [A_106,B_107,C_108,D_109] :
      ( k2_lattices(A_106,k2_lattices(A_106,B_107,C_108),D_109) = k2_lattices(A_106,B_107,k2_lattices(A_106,C_108,D_109))
      | ~ m1_subset_1(D_109,u1_struct_0(A_106))
      | ~ m1_subset_1(C_108,u1_struct_0(A_106))
      | ~ m1_subset_1(B_107,u1_struct_0(A_106))
      | ~ v7_lattices(A_106)
      | ~ l1_lattices(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_966,plain,(
    ! [B_107,C_108] :
      ( k2_lattices('#skF_8',k2_lattices('#skF_8',B_107,C_108),'#skF_11') = k2_lattices('#skF_8',B_107,k2_lattices('#skF_8',C_108,'#skF_11'))
      | ~ m1_subset_1(C_108,u1_struct_0('#skF_8'))
      | ~ m1_subset_1(B_107,u1_struct_0('#skF_8'))
      | ~ v7_lattices('#skF_8')
      | ~ l1_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_42,c_944])).

tff(c_985,plain,(
    ! [B_107,C_108] :
      ( k2_lattices('#skF_8',k2_lattices('#skF_8',B_107,C_108),'#skF_11') = k2_lattices('#skF_8',B_107,k2_lattices('#skF_8',C_108,'#skF_11'))
      | ~ m1_subset_1(C_108,u1_struct_0('#skF_8'))
      | ~ m1_subset_1(B_107,u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_54,c_966])).

tff(c_1265,plain,(
    ! [B_119,C_120] :
      ( k2_lattices('#skF_8',k2_lattices('#skF_8',B_119,C_120),'#skF_11') = k2_lattices('#skF_8',B_119,k2_lattices('#skF_8',C_120,'#skF_11'))
      | ~ m1_subset_1(C_120,u1_struct_0('#skF_8'))
      | ~ m1_subset_1(B_119,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_985])).

tff(c_2495,plain,(
    ! [B_135] :
      ( k2_lattices('#skF_8',k2_lattices('#skF_8',B_135,'#skF_10'),'#skF_11') = k2_lattices('#skF_8',B_135,k2_lattices('#skF_8','#skF_10','#skF_11'))
      | ~ m1_subset_1(B_135,u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_44,c_1265])).

tff(c_2542,plain,(
    k2_lattices('#skF_8',k2_lattices('#skF_8','#skF_9','#skF_10'),'#skF_11') = k2_lattices('#skF_8','#skF_9',k2_lattices('#skF_8','#skF_10','#skF_11')) ),
    inference(resolution,[status(thm)],[c_46,c_2495])).

tff(c_2588,plain,(
    k2_lattices('#skF_8','#skF_9',k2_lattices('#skF_8','#skF_10','#skF_11')) = k2_lattices('#skF_8','#skF_9','#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_670,c_2542])).

tff(c_2776,plain,
    ( m1_subset_1(k2_lattices('#skF_8','#skF_9','#skF_11'),u1_struct_0('#skF_8'))
    | ~ m1_subset_1(k2_lattices('#skF_8','#skF_10','#skF_11'),u1_struct_0('#skF_8'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_8'))
    | ~ l1_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_2588,c_28])).

tff(c_2786,plain,
    ( m1_subset_1(k2_lattices('#skF_8','#skF_9','#skF_11'),u1_struct_0('#skF_8'))
    | ~ m1_subset_1(k2_lattices('#skF_8','#skF_10','#skF_11'),u1_struct_0('#skF_8'))
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_46,c_2776])).

tff(c_2787,plain,
    ( m1_subset_1(k2_lattices('#skF_8','#skF_9','#skF_11'),u1_struct_0('#skF_8'))
    | ~ m1_subset_1(k2_lattices('#skF_8','#skF_10','#skF_11'),u1_struct_0('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2786])).

tff(c_2938,plain,(
    ~ m1_subset_1(k2_lattices('#skF_8','#skF_10','#skF_11'),u1_struct_0('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_2787])).

tff(c_2941,plain,
    ( ~ m1_subset_1('#skF_11',u1_struct_0('#skF_8'))
    | ~ m1_subset_1('#skF_10',u1_struct_0('#skF_8'))
    | ~ l1_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_28,c_2938])).

tff(c_2944,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_44,c_42,c_2941])).

tff(c_2946,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2944])).

tff(c_2947,plain,(
    m1_subset_1(k2_lattices('#skF_8','#skF_9','#skF_11'),u1_struct_0('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_2787])).

tff(c_432,plain,(
    ! [A_94,B_95,C_96] :
      ( r1_lattices(A_94,B_95,C_96)
      | k2_lattices(A_94,B_95,C_96) != B_95
      | ~ m1_subset_1(C_96,u1_struct_0(A_94))
      | ~ m1_subset_1(B_95,u1_struct_0(A_94))
      | ~ l3_lattices(A_94)
      | ~ v9_lattices(A_94)
      | ~ v8_lattices(A_94)
      | v2_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_9491,plain,(
    ! [A_185,B_186,B_187,C_188] :
      ( r1_lattices(A_185,B_186,k2_lattices(A_185,B_187,C_188))
      | k2_lattices(A_185,B_186,k2_lattices(A_185,B_187,C_188)) != B_186
      | ~ m1_subset_1(B_186,u1_struct_0(A_185))
      | ~ l3_lattices(A_185)
      | ~ v9_lattices(A_185)
      | ~ v8_lattices(A_185)
      | ~ m1_subset_1(C_188,u1_struct_0(A_185))
      | ~ m1_subset_1(B_187,u1_struct_0(A_185))
      | ~ l1_lattices(A_185)
      | v2_struct_0(A_185) ) ),
    inference(resolution,[status(thm)],[c_28,c_432])).

tff(c_38,plain,(
    ~ r1_lattices('#skF_8',k2_lattices('#skF_8','#skF_9','#skF_11'),k2_lattices('#skF_8','#skF_10','#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_9496,plain,
    ( k2_lattices('#skF_8',k2_lattices('#skF_8','#skF_9','#skF_11'),k2_lattices('#skF_8','#skF_10','#skF_11')) != k2_lattices('#skF_8','#skF_9','#skF_11')
    | ~ m1_subset_1(k2_lattices('#skF_8','#skF_9','#skF_11'),u1_struct_0('#skF_8'))
    | ~ l3_lattices('#skF_8')
    | ~ v9_lattices('#skF_8')
    | ~ v8_lattices('#skF_8')
    | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_8'))
    | ~ m1_subset_1('#skF_10',u1_struct_0('#skF_8'))
    | ~ l1_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_9491,c_38])).

tff(c_9722,plain,
    ( k2_lattices('#skF_8',k2_lattices('#skF_8','#skF_9','#skF_11'),k2_lattices('#skF_8','#skF_10','#skF_11')) != k2_lattices('#skF_8','#skF_9','#skF_11')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_44,c_42,c_52,c_50,c_48,c_2947,c_9496])).

tff(c_9723,plain,(
    k2_lattices('#skF_8',k2_lattices('#skF_8','#skF_9','#skF_11'),k2_lattices('#skF_8','#skF_10','#skF_11')) != k2_lattices('#skF_8','#skF_9','#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_9722])).

tff(c_120,plain,(
    ! [A_88,B_89,C_90] :
      ( k1_lattices(A_88,k2_lattices(A_88,B_89,C_90),C_90) = C_90
      | ~ m1_subset_1(C_90,u1_struct_0(A_88))
      | ~ m1_subset_1(B_89,u1_struct_0(A_88))
      | ~ v8_lattices(A_88)
      | ~ l3_lattices(A_88)
      | v2_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10044,plain,(
    ! [A_189,B_190,B_191,C_192] :
      ( k1_lattices(A_189,k2_lattices(A_189,B_190,k2_lattices(A_189,B_191,C_192)),k2_lattices(A_189,B_191,C_192)) = k2_lattices(A_189,B_191,C_192)
      | ~ m1_subset_1(B_190,u1_struct_0(A_189))
      | ~ v8_lattices(A_189)
      | ~ l3_lattices(A_189)
      | ~ m1_subset_1(C_192,u1_struct_0(A_189))
      | ~ m1_subset_1(B_191,u1_struct_0(A_189))
      | ~ l1_lattices(A_189)
      | v2_struct_0(A_189) ) ),
    inference(resolution,[status(thm)],[c_28,c_120])).

tff(c_10467,plain,
    ( k1_lattices('#skF_8',k2_lattices('#skF_8','#skF_9','#skF_11'),k2_lattices('#skF_8','#skF_10','#skF_11')) = k2_lattices('#skF_8','#skF_10','#skF_11')
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_8'))
    | ~ v8_lattices('#skF_8')
    | ~ l3_lattices('#skF_8')
    | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_8'))
    | ~ m1_subset_1('#skF_10',u1_struct_0('#skF_8'))
    | ~ l1_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_2588,c_10044])).

tff(c_10954,plain,
    ( k1_lattices('#skF_8',k2_lattices('#skF_8','#skF_9','#skF_11'),k2_lattices('#skF_8','#skF_10','#skF_11')) = k2_lattices('#skF_8','#skF_10','#skF_11')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_44,c_42,c_48,c_52,c_46,c_10467])).

tff(c_10955,plain,(
    k1_lattices('#skF_8',k2_lattices('#skF_8','#skF_9','#skF_11'),k2_lattices('#skF_8','#skF_10','#skF_11')) = k2_lattices('#skF_8','#skF_10','#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_10954])).

tff(c_77,plain,(
    ! [A_85,B_86,C_87] :
      ( k2_lattices(A_85,B_86,k1_lattices(A_85,B_86,C_87)) = B_86
      | ~ m1_subset_1(C_87,u1_struct_0(A_85))
      | ~ m1_subset_1(B_86,u1_struct_0(A_85))
      | ~ v9_lattices(A_85)
      | ~ l3_lattices(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_100,plain,(
    ! [A_49,B_86,B_50,C_51] :
      ( k2_lattices(A_49,B_86,k1_lattices(A_49,B_86,k2_lattices(A_49,B_50,C_51))) = B_86
      | ~ m1_subset_1(B_86,u1_struct_0(A_49))
      | ~ v9_lattices(A_49)
      | ~ l3_lattices(A_49)
      | ~ m1_subset_1(C_51,u1_struct_0(A_49))
      | ~ m1_subset_1(B_50,u1_struct_0(A_49))
      | ~ l1_lattices(A_49)
      | v2_struct_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_28,c_77])).

tff(c_11138,plain,
    ( k2_lattices('#skF_8',k2_lattices('#skF_8','#skF_9','#skF_11'),k2_lattices('#skF_8','#skF_10','#skF_11')) = k2_lattices('#skF_8','#skF_9','#skF_11')
    | ~ m1_subset_1(k2_lattices('#skF_8','#skF_9','#skF_11'),u1_struct_0('#skF_8'))
    | ~ v9_lattices('#skF_8')
    | ~ l3_lattices('#skF_8')
    | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_8'))
    | ~ m1_subset_1('#skF_10',u1_struct_0('#skF_8'))
    | ~ l1_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_10955,c_100])).

tff(c_11145,plain,
    ( k2_lattices('#skF_8',k2_lattices('#skF_8','#skF_9','#skF_11'),k2_lattices('#skF_8','#skF_10','#skF_11')) = k2_lattices('#skF_8','#skF_9','#skF_11')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_44,c_42,c_48,c_50,c_2947,c_11138])).

tff(c_11147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_9723,c_11145])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:34:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.62/3.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.62/3.58  
% 9.62/3.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.62/3.58  %$ r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v2_struct_0 > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > #skF_7 > #skF_5 > #skF_2 > #skF_4 > #skF_11 > #skF_1 > #skF_10 > #skF_9 > #skF_8 > #skF_3 > #skF_6
% 9.62/3.58  
% 9.62/3.58  %Foreground sorts:
% 9.62/3.58  
% 9.62/3.58  
% 9.62/3.58  %Background operators:
% 9.62/3.58  
% 9.62/3.58  
% 9.62/3.58  %Foreground operators:
% 9.62/3.58  tff(l3_lattices, type, l3_lattices: $i > $o).
% 9.62/3.58  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.62/3.58  tff('#skF_7', type, '#skF_7': $i > $i).
% 9.62/3.58  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 9.62/3.58  tff('#skF_5', type, '#skF_5': $i > $i).
% 9.62/3.58  tff(l2_lattices, type, l2_lattices: $i > $o).
% 9.62/3.58  tff('#skF_2', type, '#skF_2': $i > $i).
% 9.62/3.58  tff('#skF_4', type, '#skF_4': $i > $i).
% 9.62/3.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.62/3.58  tff('#skF_11', type, '#skF_11': $i).
% 9.62/3.58  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.62/3.58  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 9.62/3.58  tff(l1_lattices, type, l1_lattices: $i > $o).
% 9.62/3.58  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 9.62/3.58  tff('#skF_10', type, '#skF_10': $i).
% 9.62/3.58  tff(v9_lattices, type, v9_lattices: $i > $o).
% 9.62/3.58  tff('#skF_9', type, '#skF_9': $i).
% 9.62/3.58  tff('#skF_8', type, '#skF_8': $i).
% 9.62/3.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.62/3.58  tff('#skF_3', type, '#skF_3': $i > $i).
% 9.62/3.58  tff(v8_lattices, type, v8_lattices: $i > $o).
% 9.62/3.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.62/3.58  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.62/3.58  tff('#skF_6', type, '#skF_6': $i > $i).
% 9.62/3.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.62/3.58  tff(v7_lattices, type, v7_lattices: $i > $o).
% 9.62/3.58  
% 9.62/3.60  tff(f_134, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_lattices(A, B, C) => r1_lattices(A, k2_lattices(A, B, D), k2_lattices(A, C, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_lattices)).
% 9.62/3.60  tff(f_90, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 9.62/3.60  tff(f_84, axiom, (![A, B, C]: ((((~v2_struct_0(A) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k2_lattices(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_lattices)).
% 9.62/3.60  tff(f_109, axiom, (![A]: ((((~v2_struct_0(A) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k2_lattices(A, B, C) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 9.62/3.60  tff(f_43, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v7_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (k2_lattices(A, B, k2_lattices(A, C, D)) = k2_lattices(A, k2_lattices(A, B, C), D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_lattices)).
% 9.62/3.60  tff(f_58, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v8_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k1_lattices(A, k2_lattices(A, B, C), C) = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattices)).
% 9.62/3.60  tff(f_73, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v9_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k2_lattices(A, B, k1_lattices(A, B, C)) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattices)).
% 9.62/3.60  tff(c_56, plain, (~v2_struct_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.62/3.60  tff(c_48, plain, (l3_lattices('#skF_8')), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.62/3.60  tff(c_62, plain, (![A_72]: (l1_lattices(A_72) | ~l3_lattices(A_72))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.62/3.60  tff(c_66, plain, (l1_lattices('#skF_8')), inference(resolution, [status(thm)], [c_48, c_62])).
% 9.62/3.60  tff(c_44, plain, (m1_subset_1('#skF_10', u1_struct_0('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.62/3.60  tff(c_42, plain, (m1_subset_1('#skF_11', u1_struct_0('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.62/3.60  tff(c_52, plain, (v8_lattices('#skF_8')), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.62/3.60  tff(c_50, plain, (v9_lattices('#skF_8')), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.62/3.60  tff(c_28, plain, (![A_49, B_50, C_51]: (m1_subset_1(k2_lattices(A_49, B_50, C_51), u1_struct_0(A_49)) | ~m1_subset_1(C_51, u1_struct_0(A_49)) | ~m1_subset_1(B_50, u1_struct_0(A_49)) | ~l1_lattices(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.62/3.60  tff(c_46, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.62/3.60  tff(c_40, plain, (r1_lattices('#skF_8', '#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.62/3.60  tff(c_664, plain, (![A_99, B_100, C_101]: (k2_lattices(A_99, B_100, C_101)=B_100 | ~r1_lattices(A_99, B_100, C_101) | ~m1_subset_1(C_101, u1_struct_0(A_99)) | ~m1_subset_1(B_100, u1_struct_0(A_99)) | ~l3_lattices(A_99) | ~v9_lattices(A_99) | ~v8_lattices(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.62/3.60  tff(c_666, plain, (k2_lattices('#skF_8', '#skF_9', '#skF_10')='#skF_9' | ~m1_subset_1('#skF_10', u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_8')) | ~l3_lattices('#skF_8') | ~v9_lattices('#skF_8') | ~v8_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_40, c_664])).
% 9.62/3.60  tff(c_669, plain, (k2_lattices('#skF_8', '#skF_9', '#skF_10')='#skF_9' | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_44, c_666])).
% 9.62/3.60  tff(c_670, plain, (k2_lattices('#skF_8', '#skF_9', '#skF_10')='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_56, c_669])).
% 9.62/3.60  tff(c_54, plain, (v7_lattices('#skF_8')), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.62/3.60  tff(c_944, plain, (![A_106, B_107, C_108, D_109]: (k2_lattices(A_106, k2_lattices(A_106, B_107, C_108), D_109)=k2_lattices(A_106, B_107, k2_lattices(A_106, C_108, D_109)) | ~m1_subset_1(D_109, u1_struct_0(A_106)) | ~m1_subset_1(C_108, u1_struct_0(A_106)) | ~m1_subset_1(B_107, u1_struct_0(A_106)) | ~v7_lattices(A_106) | ~l1_lattices(A_106) | v2_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.62/3.60  tff(c_966, plain, (![B_107, C_108]: (k2_lattices('#skF_8', k2_lattices('#skF_8', B_107, C_108), '#skF_11')=k2_lattices('#skF_8', B_107, k2_lattices('#skF_8', C_108, '#skF_11')) | ~m1_subset_1(C_108, u1_struct_0('#skF_8')) | ~m1_subset_1(B_107, u1_struct_0('#skF_8')) | ~v7_lattices('#skF_8') | ~l1_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_42, c_944])).
% 9.62/3.60  tff(c_985, plain, (![B_107, C_108]: (k2_lattices('#skF_8', k2_lattices('#skF_8', B_107, C_108), '#skF_11')=k2_lattices('#skF_8', B_107, k2_lattices('#skF_8', C_108, '#skF_11')) | ~m1_subset_1(C_108, u1_struct_0('#skF_8')) | ~m1_subset_1(B_107, u1_struct_0('#skF_8')) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_54, c_966])).
% 9.62/3.60  tff(c_1265, plain, (![B_119, C_120]: (k2_lattices('#skF_8', k2_lattices('#skF_8', B_119, C_120), '#skF_11')=k2_lattices('#skF_8', B_119, k2_lattices('#skF_8', C_120, '#skF_11')) | ~m1_subset_1(C_120, u1_struct_0('#skF_8')) | ~m1_subset_1(B_119, u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_56, c_985])).
% 9.62/3.60  tff(c_2495, plain, (![B_135]: (k2_lattices('#skF_8', k2_lattices('#skF_8', B_135, '#skF_10'), '#skF_11')=k2_lattices('#skF_8', B_135, k2_lattices('#skF_8', '#skF_10', '#skF_11')) | ~m1_subset_1(B_135, u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_44, c_1265])).
% 9.62/3.60  tff(c_2542, plain, (k2_lattices('#skF_8', k2_lattices('#skF_8', '#skF_9', '#skF_10'), '#skF_11')=k2_lattices('#skF_8', '#skF_9', k2_lattices('#skF_8', '#skF_10', '#skF_11'))), inference(resolution, [status(thm)], [c_46, c_2495])).
% 9.62/3.60  tff(c_2588, plain, (k2_lattices('#skF_8', '#skF_9', k2_lattices('#skF_8', '#skF_10', '#skF_11'))=k2_lattices('#skF_8', '#skF_9', '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_670, c_2542])).
% 9.62/3.60  tff(c_2776, plain, (m1_subset_1(k2_lattices('#skF_8', '#skF_9', '#skF_11'), u1_struct_0('#skF_8')) | ~m1_subset_1(k2_lattices('#skF_8', '#skF_10', '#skF_11'), u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_8')) | ~l1_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_2588, c_28])).
% 9.62/3.60  tff(c_2786, plain, (m1_subset_1(k2_lattices('#skF_8', '#skF_9', '#skF_11'), u1_struct_0('#skF_8')) | ~m1_subset_1(k2_lattices('#skF_8', '#skF_10', '#skF_11'), u1_struct_0('#skF_8')) | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_46, c_2776])).
% 9.62/3.60  tff(c_2787, plain, (m1_subset_1(k2_lattices('#skF_8', '#skF_9', '#skF_11'), u1_struct_0('#skF_8')) | ~m1_subset_1(k2_lattices('#skF_8', '#skF_10', '#skF_11'), u1_struct_0('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_56, c_2786])).
% 9.62/3.60  tff(c_2938, plain, (~m1_subset_1(k2_lattices('#skF_8', '#skF_10', '#skF_11'), u1_struct_0('#skF_8'))), inference(splitLeft, [status(thm)], [c_2787])).
% 9.62/3.60  tff(c_2941, plain, (~m1_subset_1('#skF_11', u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_10', u1_struct_0('#skF_8')) | ~l1_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_28, c_2938])).
% 9.62/3.60  tff(c_2944, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_44, c_42, c_2941])).
% 9.62/3.60  tff(c_2946, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_2944])).
% 9.62/3.60  tff(c_2947, plain, (m1_subset_1(k2_lattices('#skF_8', '#skF_9', '#skF_11'), u1_struct_0('#skF_8'))), inference(splitRight, [status(thm)], [c_2787])).
% 9.62/3.60  tff(c_432, plain, (![A_94, B_95, C_96]: (r1_lattices(A_94, B_95, C_96) | k2_lattices(A_94, B_95, C_96)!=B_95 | ~m1_subset_1(C_96, u1_struct_0(A_94)) | ~m1_subset_1(B_95, u1_struct_0(A_94)) | ~l3_lattices(A_94) | ~v9_lattices(A_94) | ~v8_lattices(A_94) | v2_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.62/3.60  tff(c_9491, plain, (![A_185, B_186, B_187, C_188]: (r1_lattices(A_185, B_186, k2_lattices(A_185, B_187, C_188)) | k2_lattices(A_185, B_186, k2_lattices(A_185, B_187, C_188))!=B_186 | ~m1_subset_1(B_186, u1_struct_0(A_185)) | ~l3_lattices(A_185) | ~v9_lattices(A_185) | ~v8_lattices(A_185) | ~m1_subset_1(C_188, u1_struct_0(A_185)) | ~m1_subset_1(B_187, u1_struct_0(A_185)) | ~l1_lattices(A_185) | v2_struct_0(A_185))), inference(resolution, [status(thm)], [c_28, c_432])).
% 9.62/3.60  tff(c_38, plain, (~r1_lattices('#skF_8', k2_lattices('#skF_8', '#skF_9', '#skF_11'), k2_lattices('#skF_8', '#skF_10', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.62/3.60  tff(c_9496, plain, (k2_lattices('#skF_8', k2_lattices('#skF_8', '#skF_9', '#skF_11'), k2_lattices('#skF_8', '#skF_10', '#skF_11'))!=k2_lattices('#skF_8', '#skF_9', '#skF_11') | ~m1_subset_1(k2_lattices('#skF_8', '#skF_9', '#skF_11'), u1_struct_0('#skF_8')) | ~l3_lattices('#skF_8') | ~v9_lattices('#skF_8') | ~v8_lattices('#skF_8') | ~m1_subset_1('#skF_11', u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_10', u1_struct_0('#skF_8')) | ~l1_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_9491, c_38])).
% 9.62/3.60  tff(c_9722, plain, (k2_lattices('#skF_8', k2_lattices('#skF_8', '#skF_9', '#skF_11'), k2_lattices('#skF_8', '#skF_10', '#skF_11'))!=k2_lattices('#skF_8', '#skF_9', '#skF_11') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_44, c_42, c_52, c_50, c_48, c_2947, c_9496])).
% 9.62/3.60  tff(c_9723, plain, (k2_lattices('#skF_8', k2_lattices('#skF_8', '#skF_9', '#skF_11'), k2_lattices('#skF_8', '#skF_10', '#skF_11'))!=k2_lattices('#skF_8', '#skF_9', '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_56, c_9722])).
% 9.62/3.60  tff(c_120, plain, (![A_88, B_89, C_90]: (k1_lattices(A_88, k2_lattices(A_88, B_89, C_90), C_90)=C_90 | ~m1_subset_1(C_90, u1_struct_0(A_88)) | ~m1_subset_1(B_89, u1_struct_0(A_88)) | ~v8_lattices(A_88) | ~l3_lattices(A_88) | v2_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.62/3.60  tff(c_10044, plain, (![A_189, B_190, B_191, C_192]: (k1_lattices(A_189, k2_lattices(A_189, B_190, k2_lattices(A_189, B_191, C_192)), k2_lattices(A_189, B_191, C_192))=k2_lattices(A_189, B_191, C_192) | ~m1_subset_1(B_190, u1_struct_0(A_189)) | ~v8_lattices(A_189) | ~l3_lattices(A_189) | ~m1_subset_1(C_192, u1_struct_0(A_189)) | ~m1_subset_1(B_191, u1_struct_0(A_189)) | ~l1_lattices(A_189) | v2_struct_0(A_189))), inference(resolution, [status(thm)], [c_28, c_120])).
% 9.62/3.60  tff(c_10467, plain, (k1_lattices('#skF_8', k2_lattices('#skF_8', '#skF_9', '#skF_11'), k2_lattices('#skF_8', '#skF_10', '#skF_11'))=k2_lattices('#skF_8', '#skF_10', '#skF_11') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_8')) | ~v8_lattices('#skF_8') | ~l3_lattices('#skF_8') | ~m1_subset_1('#skF_11', u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_10', u1_struct_0('#skF_8')) | ~l1_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_2588, c_10044])).
% 9.62/3.60  tff(c_10954, plain, (k1_lattices('#skF_8', k2_lattices('#skF_8', '#skF_9', '#skF_11'), k2_lattices('#skF_8', '#skF_10', '#skF_11'))=k2_lattices('#skF_8', '#skF_10', '#skF_11') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_44, c_42, c_48, c_52, c_46, c_10467])).
% 9.62/3.60  tff(c_10955, plain, (k1_lattices('#skF_8', k2_lattices('#skF_8', '#skF_9', '#skF_11'), k2_lattices('#skF_8', '#skF_10', '#skF_11'))=k2_lattices('#skF_8', '#skF_10', '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_56, c_10954])).
% 9.62/3.60  tff(c_77, plain, (![A_85, B_86, C_87]: (k2_lattices(A_85, B_86, k1_lattices(A_85, B_86, C_87))=B_86 | ~m1_subset_1(C_87, u1_struct_0(A_85)) | ~m1_subset_1(B_86, u1_struct_0(A_85)) | ~v9_lattices(A_85) | ~l3_lattices(A_85) | v2_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.62/3.60  tff(c_100, plain, (![A_49, B_86, B_50, C_51]: (k2_lattices(A_49, B_86, k1_lattices(A_49, B_86, k2_lattices(A_49, B_50, C_51)))=B_86 | ~m1_subset_1(B_86, u1_struct_0(A_49)) | ~v9_lattices(A_49) | ~l3_lattices(A_49) | ~m1_subset_1(C_51, u1_struct_0(A_49)) | ~m1_subset_1(B_50, u1_struct_0(A_49)) | ~l1_lattices(A_49) | v2_struct_0(A_49))), inference(resolution, [status(thm)], [c_28, c_77])).
% 9.62/3.60  tff(c_11138, plain, (k2_lattices('#skF_8', k2_lattices('#skF_8', '#skF_9', '#skF_11'), k2_lattices('#skF_8', '#skF_10', '#skF_11'))=k2_lattices('#skF_8', '#skF_9', '#skF_11') | ~m1_subset_1(k2_lattices('#skF_8', '#skF_9', '#skF_11'), u1_struct_0('#skF_8')) | ~v9_lattices('#skF_8') | ~l3_lattices('#skF_8') | ~m1_subset_1('#skF_11', u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_10', u1_struct_0('#skF_8')) | ~l1_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_10955, c_100])).
% 9.62/3.60  tff(c_11145, plain, (k2_lattices('#skF_8', k2_lattices('#skF_8', '#skF_9', '#skF_11'), k2_lattices('#skF_8', '#skF_10', '#skF_11'))=k2_lattices('#skF_8', '#skF_9', '#skF_11') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_44, c_42, c_48, c_50, c_2947, c_11138])).
% 9.62/3.60  tff(c_11147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_9723, c_11145])).
% 9.62/3.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.62/3.60  
% 9.62/3.60  Inference rules
% 9.62/3.60  ----------------------
% 9.62/3.60  #Ref     : 0
% 9.62/3.60  #Sup     : 2265
% 9.62/3.60  #Fact    : 0
% 9.62/3.60  #Define  : 0
% 9.62/3.60  #Split   : 16
% 9.62/3.60  #Chain   : 0
% 9.62/3.60  #Close   : 0
% 9.62/3.60  
% 9.62/3.60  Ordering : KBO
% 9.62/3.60  
% 9.62/3.60  Simplification rules
% 9.62/3.60  ----------------------
% 9.62/3.60  #Subsume      : 129
% 9.62/3.60  #Demod        : 5012
% 9.62/3.60  #Tautology    : 1146
% 9.62/3.60  #SimpNegUnit  : 941
% 9.62/3.60  #BackRed      : 18
% 9.62/3.60  
% 9.62/3.60  #Partial instantiations: 0
% 9.62/3.60  #Strategies tried      : 1
% 9.62/3.60  
% 9.62/3.60  Timing (in seconds)
% 9.62/3.60  ----------------------
% 9.62/3.60  Preprocessing        : 0.33
% 9.62/3.60  Parsing              : 0.18
% 9.62/3.60  CNF conversion       : 0.03
% 9.62/3.60  Main loop            : 2.50
% 9.62/3.60  Inferencing          : 0.69
% 9.62/3.60  Reduction            : 1.11
% 9.62/3.60  Demodulation         : 0.89
% 9.62/3.60  BG Simplification    : 0.07
% 9.62/3.60  Subsumption          : 0.51
% 9.62/3.60  Abstraction          : 0.11
% 9.62/3.60  MUC search           : 0.00
% 9.62/3.60  Cooper               : 0.00
% 9.62/3.60  Total                : 2.86
% 9.62/3.60  Index Insertion      : 0.00
% 9.62/3.60  Index Deletion       : 0.00
% 9.62/3.60  Index Matching       : 0.00
% 9.62/3.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
