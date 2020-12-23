%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:13 EST 2020

% Result     : Theorem 7.92s
% Output     : CNFRefutation 7.92s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 225 expanded)
%              Number of leaves         :   33 (  99 expanded)
%              Depth                    :   13
%              Number of atoms          :  190 ( 895 expanded)
%              Number of equality atoms :   32 (  45 expanded)
%              Maximal formula depth    :   13 (   4 average)
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

tff(f_130,negated_conjecture,(
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

tff(f_105,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k2_lattices(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_lattices)).

tff(f_58,axiom,(
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

tff(f_40,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_lattices(A,B,C)
              <=> k1_lattices(A,B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).

tff(f_88,axiom,(
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

tff(f_73,axiom,(
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

tff(c_56,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_48,plain,(
    l3_lattices('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_62,plain,(
    ! [A_72] :
      ( l1_lattices(A_72)
      | ~ l3_lattices(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_66,plain,(
    l1_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_62])).

tff(c_44,plain,(
    m1_subset_1('#skF_10',u1_struct_0('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_42,plain,(
    m1_subset_1('#skF_11',u1_struct_0('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_57,plain,(
    ! [A_71] :
      ( l2_lattices(A_71)
      | ~ l3_lattices(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_61,plain,(
    l2_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_57])).

tff(c_46,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_32,plain,(
    ! [A_56,B_57,C_58] :
      ( m1_subset_1(k2_lattices(A_56,B_57,C_58),u1_struct_0(A_56))
      | ~ m1_subset_1(C_58,u1_struct_0(A_56))
      | ~ m1_subset_1(B_57,u1_struct_0(A_56))
      | ~ l1_lattices(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_54,plain,(
    v7_lattices('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_923,plain,(
    ! [A_106,B_107,C_108,D_109] :
      ( k2_lattices(A_106,k2_lattices(A_106,B_107,C_108),D_109) = k2_lattices(A_106,B_107,k2_lattices(A_106,C_108,D_109))
      | ~ m1_subset_1(D_109,u1_struct_0(A_106))
      | ~ m1_subset_1(C_108,u1_struct_0(A_106))
      | ~ m1_subset_1(B_107,u1_struct_0(A_106))
      | ~ v7_lattices(A_106)
      | ~ l1_lattices(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_945,plain,(
    ! [B_107,C_108] :
      ( k2_lattices('#skF_8',k2_lattices('#skF_8',B_107,C_108),'#skF_11') = k2_lattices('#skF_8',B_107,k2_lattices('#skF_8',C_108,'#skF_11'))
      | ~ m1_subset_1(C_108,u1_struct_0('#skF_8'))
      | ~ m1_subset_1(B_107,u1_struct_0('#skF_8'))
      | ~ v7_lattices('#skF_8')
      | ~ l1_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_42,c_923])).

tff(c_964,plain,(
    ! [B_107,C_108] :
      ( k2_lattices('#skF_8',k2_lattices('#skF_8',B_107,C_108),'#skF_11') = k2_lattices('#skF_8',B_107,k2_lattices('#skF_8',C_108,'#skF_11'))
      | ~ m1_subset_1(C_108,u1_struct_0('#skF_8'))
      | ~ m1_subset_1(B_107,u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_54,c_945])).

tff(c_1775,plain,(
    ! [B_127,C_128] :
      ( k2_lattices('#skF_8',k2_lattices('#skF_8',B_127,C_128),'#skF_11') = k2_lattices('#skF_8',B_127,k2_lattices('#skF_8',C_128,'#skF_11'))
      | ~ m1_subset_1(C_128,u1_struct_0('#skF_8'))
      | ~ m1_subset_1(B_127,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_964])).

tff(c_2939,plain,(
    ! [B_142] :
      ( k2_lattices('#skF_8',k2_lattices('#skF_8',B_142,'#skF_11'),'#skF_11') = k2_lattices('#skF_8',B_142,k2_lattices('#skF_8','#skF_11','#skF_11'))
      | ~ m1_subset_1(B_142,u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_42,c_1775])).

tff(c_3025,plain,(
    k2_lattices('#skF_8',k2_lattices('#skF_8','#skF_9','#skF_11'),'#skF_11') = k2_lattices('#skF_8','#skF_9',k2_lattices('#skF_8','#skF_11','#skF_11')) ),
    inference(resolution,[status(thm)],[c_46,c_2939])).

tff(c_3043,plain,
    ( m1_subset_1(k2_lattices('#skF_8','#skF_9',k2_lattices('#skF_8','#skF_11','#skF_11')),u1_struct_0('#skF_8'))
    | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_8'))
    | ~ m1_subset_1(k2_lattices('#skF_8','#skF_9','#skF_11'),u1_struct_0('#skF_8'))
    | ~ l1_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_3025,c_32])).

tff(c_3055,plain,
    ( m1_subset_1(k2_lattices('#skF_8','#skF_9',k2_lattices('#skF_8','#skF_11','#skF_11')),u1_struct_0('#skF_8'))
    | ~ m1_subset_1(k2_lattices('#skF_8','#skF_9','#skF_11'),u1_struct_0('#skF_8'))
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_42,c_3043])).

tff(c_3056,plain,
    ( m1_subset_1(k2_lattices('#skF_8','#skF_9',k2_lattices('#skF_8','#skF_11','#skF_11')),u1_struct_0('#skF_8'))
    | ~ m1_subset_1(k2_lattices('#skF_8','#skF_9','#skF_11'),u1_struct_0('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_3055])).

tff(c_3777,plain,(
    ~ m1_subset_1(k2_lattices('#skF_8','#skF_9','#skF_11'),u1_struct_0('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_3056])).

tff(c_3780,plain,
    ( ~ m1_subset_1('#skF_11',u1_struct_0('#skF_8'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_8'))
    | ~ l1_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_32,c_3777])).

tff(c_3783,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_46,c_42,c_3780])).

tff(c_3785,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_3783])).

tff(c_3787,plain,(
    m1_subset_1(k2_lattices('#skF_8','#skF_9','#skF_11'),u1_struct_0('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_3056])).

tff(c_77,plain,(
    ! [A_85,B_86,C_87] :
      ( r1_lattices(A_85,B_86,C_87)
      | k1_lattices(A_85,B_86,C_87) != C_87
      | ~ m1_subset_1(C_87,u1_struct_0(A_85))
      | ~ m1_subset_1(B_86,u1_struct_0(A_85))
      | ~ l2_lattices(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_7775,plain,(
    ! [A_187,B_188,B_189,C_190] :
      ( r1_lattices(A_187,B_188,k2_lattices(A_187,B_189,C_190))
      | k1_lattices(A_187,B_188,k2_lattices(A_187,B_189,C_190)) != k2_lattices(A_187,B_189,C_190)
      | ~ m1_subset_1(B_188,u1_struct_0(A_187))
      | ~ l2_lattices(A_187)
      | ~ m1_subset_1(C_190,u1_struct_0(A_187))
      | ~ m1_subset_1(B_189,u1_struct_0(A_187))
      | ~ l1_lattices(A_187)
      | v2_struct_0(A_187) ) ),
    inference(resolution,[status(thm)],[c_32,c_77])).

tff(c_38,plain,(
    ~ r1_lattices('#skF_8',k2_lattices('#skF_8','#skF_9','#skF_11'),k2_lattices('#skF_8','#skF_10','#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_7780,plain,
    ( k1_lattices('#skF_8',k2_lattices('#skF_8','#skF_9','#skF_11'),k2_lattices('#skF_8','#skF_10','#skF_11')) != k2_lattices('#skF_8','#skF_10','#skF_11')
    | ~ m1_subset_1(k2_lattices('#skF_8','#skF_9','#skF_11'),u1_struct_0('#skF_8'))
    | ~ l2_lattices('#skF_8')
    | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_8'))
    | ~ m1_subset_1('#skF_10',u1_struct_0('#skF_8'))
    | ~ l1_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_7775,c_38])).

tff(c_7952,plain,
    ( k1_lattices('#skF_8',k2_lattices('#skF_8','#skF_9','#skF_11'),k2_lattices('#skF_8','#skF_10','#skF_11')) != k2_lattices('#skF_8','#skF_10','#skF_11')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_44,c_42,c_61,c_3787,c_7780])).

tff(c_7953,plain,(
    k1_lattices('#skF_8',k2_lattices('#skF_8','#skF_9','#skF_11'),k2_lattices('#skF_8','#skF_10','#skF_11')) != k2_lattices('#skF_8','#skF_10','#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_7952])).

tff(c_52,plain,(
    v8_lattices('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_40,plain,(
    r1_lattices('#skF_8','#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_120,plain,(
    ! [A_88,B_89,C_90] :
      ( k1_lattices(A_88,B_89,C_90) = C_90
      | ~ r1_lattices(A_88,B_89,C_90)
      | ~ m1_subset_1(C_90,u1_struct_0(A_88))
      | ~ m1_subset_1(B_89,u1_struct_0(A_88))
      | ~ l2_lattices(A_88)
      | v2_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_122,plain,
    ( k1_lattices('#skF_8','#skF_9','#skF_10') = '#skF_10'
    | ~ m1_subset_1('#skF_10',u1_struct_0('#skF_8'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_8'))
    | ~ l2_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_40,c_120])).

tff(c_125,plain,
    ( k1_lattices('#skF_8','#skF_9','#skF_10') = '#skF_10'
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_46,c_44,c_122])).

tff(c_126,plain,(
    k1_lattices('#skF_8','#skF_9','#skF_10') = '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_125])).

tff(c_50,plain,(
    v9_lattices('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_288,plain,(
    ! [A_93,B_94,C_95] :
      ( k2_lattices(A_93,B_94,k1_lattices(A_93,B_94,C_95)) = B_94
      | ~ m1_subset_1(C_95,u1_struct_0(A_93))
      | ~ m1_subset_1(B_94,u1_struct_0(A_93))
      | ~ v9_lattices(A_93)
      | ~ l3_lattices(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_308,plain,(
    ! [B_94] :
      ( k2_lattices('#skF_8',B_94,k1_lattices('#skF_8',B_94,'#skF_10')) = B_94
      | ~ m1_subset_1(B_94,u1_struct_0('#skF_8'))
      | ~ v9_lattices('#skF_8')
      | ~ l3_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_44,c_288])).

tff(c_325,plain,(
    ! [B_94] :
      ( k2_lattices('#skF_8',B_94,k1_lattices('#skF_8',B_94,'#skF_10')) = B_94
      | ~ m1_subset_1(B_94,u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_308])).

tff(c_473,plain,(
    ! [B_100] :
      ( k2_lattices('#skF_8',B_100,k1_lattices('#skF_8',B_100,'#skF_10')) = B_100
      | ~ m1_subset_1(B_100,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_325])).

tff(c_499,plain,(
    k2_lattices('#skF_8','#skF_9',k1_lattices('#skF_8','#skF_9','#skF_10')) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_46,c_473])).

tff(c_537,plain,(
    k2_lattices('#skF_8','#skF_9','#skF_10') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_499])).

tff(c_6078,plain,(
    ! [B_179] :
      ( k2_lattices('#skF_8',k2_lattices('#skF_8',B_179,'#skF_10'),'#skF_11') = k2_lattices('#skF_8',B_179,k2_lattices('#skF_8','#skF_10','#skF_11'))
      | ~ m1_subset_1(B_179,u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_44,c_1775])).

tff(c_6137,plain,(
    k2_lattices('#skF_8',k2_lattices('#skF_8','#skF_9','#skF_10'),'#skF_11') = k2_lattices('#skF_8','#skF_9',k2_lattices('#skF_8','#skF_10','#skF_11')) ),
    inference(resolution,[status(thm)],[c_46,c_6078])).

tff(c_6190,plain,(
    k2_lattices('#skF_8','#skF_9',k2_lattices('#skF_8','#skF_10','#skF_11')) = k2_lattices('#skF_8','#skF_9','#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_537,c_6137])).

tff(c_420,plain,(
    ! [A_97,B_98,C_99] :
      ( k1_lattices(A_97,k2_lattices(A_97,B_98,C_99),C_99) = C_99
      | ~ m1_subset_1(C_99,u1_struct_0(A_97))
      | ~ m1_subset_1(B_98,u1_struct_0(A_97))
      | ~ v8_lattices(A_97)
      | ~ l3_lattices(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8220,plain,(
    ! [A_191,B_192,B_193,C_194] :
      ( k1_lattices(A_191,k2_lattices(A_191,B_192,k2_lattices(A_191,B_193,C_194)),k2_lattices(A_191,B_193,C_194)) = k2_lattices(A_191,B_193,C_194)
      | ~ m1_subset_1(B_192,u1_struct_0(A_191))
      | ~ v8_lattices(A_191)
      | ~ l3_lattices(A_191)
      | ~ m1_subset_1(C_194,u1_struct_0(A_191))
      | ~ m1_subset_1(B_193,u1_struct_0(A_191))
      | ~ l1_lattices(A_191)
      | v2_struct_0(A_191) ) ),
    inference(resolution,[status(thm)],[c_32,c_420])).

tff(c_8309,plain,
    ( k1_lattices('#skF_8',k2_lattices('#skF_8','#skF_9','#skF_11'),k2_lattices('#skF_8','#skF_10','#skF_11')) = k2_lattices('#skF_8','#skF_10','#skF_11')
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_8'))
    | ~ v8_lattices('#skF_8')
    | ~ l3_lattices('#skF_8')
    | ~ m1_subset_1('#skF_11',u1_struct_0('#skF_8'))
    | ~ m1_subset_1('#skF_10',u1_struct_0('#skF_8'))
    | ~ l1_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_6190,c_8220])).

tff(c_8697,plain,
    ( k1_lattices('#skF_8',k2_lattices('#skF_8','#skF_9','#skF_11'),k2_lattices('#skF_8','#skF_10','#skF_11')) = k2_lattices('#skF_8','#skF_10','#skF_11')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_44,c_42,c_48,c_52,c_46,c_8309])).

tff(c_8699,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_7953,c_8697])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n004.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 20:54:08 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.92/2.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.92/2.77  
% 7.92/2.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.92/2.77  %$ r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v2_struct_0 > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > #skF_7 > #skF_5 > #skF_2 > #skF_4 > #skF_11 > #skF_1 > #skF_10 > #skF_9 > #skF_8 > #skF_3 > #skF_6
% 7.92/2.77  
% 7.92/2.77  %Foreground sorts:
% 7.92/2.77  
% 7.92/2.77  
% 7.92/2.77  %Background operators:
% 7.92/2.77  
% 7.92/2.77  
% 7.92/2.77  %Foreground operators:
% 7.92/2.77  tff(l3_lattices, type, l3_lattices: $i > $o).
% 7.92/2.77  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.92/2.77  tff('#skF_7', type, '#skF_7': $i > $i).
% 7.92/2.77  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 7.92/2.77  tff('#skF_5', type, '#skF_5': $i > $i).
% 7.92/2.77  tff(l2_lattices, type, l2_lattices: $i > $o).
% 7.92/2.77  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.92/2.77  tff('#skF_4', type, '#skF_4': $i > $i).
% 7.92/2.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.92/2.77  tff('#skF_11', type, '#skF_11': $i).
% 7.92/2.77  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.92/2.77  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 7.92/2.77  tff(l1_lattices, type, l1_lattices: $i > $o).
% 7.92/2.77  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 7.92/2.77  tff('#skF_10', type, '#skF_10': $i).
% 7.92/2.77  tff(v9_lattices, type, v9_lattices: $i > $o).
% 7.92/2.77  tff('#skF_9', type, '#skF_9': $i).
% 7.92/2.77  tff('#skF_8', type, '#skF_8': $i).
% 7.92/2.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.92/2.77  tff('#skF_3', type, '#skF_3': $i > $i).
% 7.92/2.77  tff(v8_lattices, type, v8_lattices: $i > $o).
% 7.92/2.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.92/2.77  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.92/2.77  tff('#skF_6', type, '#skF_6': $i > $i).
% 7.92/2.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.92/2.77  tff(v7_lattices, type, v7_lattices: $i > $o).
% 7.92/2.77  
% 7.92/2.79  tff(f_130, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_lattices(A, B, C) => r1_lattices(A, k2_lattices(A, B, D), k2_lattices(A, C, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_lattices)).
% 7.92/2.79  tff(f_105, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 7.92/2.79  tff(f_99, axiom, (![A, B, C]: ((((~v2_struct_0(A) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k2_lattices(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_lattices)).
% 7.92/2.79  tff(f_58, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v7_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (k2_lattices(A, B, k2_lattices(A, C, D)) = k2_lattices(A, k2_lattices(A, B, C), D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_lattices)).
% 7.92/2.79  tff(f_40, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k1_lattices(A, B, C) = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_lattices)).
% 7.92/2.79  tff(f_88, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v9_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k2_lattices(A, B, k1_lattices(A, B, C)) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattices)).
% 7.92/2.79  tff(f_73, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v8_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k1_lattices(A, k2_lattices(A, B, C), C) = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattices)).
% 7.92/2.79  tff(c_56, plain, (~v2_struct_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.92/2.79  tff(c_48, plain, (l3_lattices('#skF_8')), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.92/2.79  tff(c_62, plain, (![A_72]: (l1_lattices(A_72) | ~l3_lattices(A_72))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.92/2.79  tff(c_66, plain, (l1_lattices('#skF_8')), inference(resolution, [status(thm)], [c_48, c_62])).
% 7.92/2.79  tff(c_44, plain, (m1_subset_1('#skF_10', u1_struct_0('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.92/2.79  tff(c_42, plain, (m1_subset_1('#skF_11', u1_struct_0('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.92/2.79  tff(c_57, plain, (![A_71]: (l2_lattices(A_71) | ~l3_lattices(A_71))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.92/2.79  tff(c_61, plain, (l2_lattices('#skF_8')), inference(resolution, [status(thm)], [c_48, c_57])).
% 7.92/2.79  tff(c_46, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.92/2.79  tff(c_32, plain, (![A_56, B_57, C_58]: (m1_subset_1(k2_lattices(A_56, B_57, C_58), u1_struct_0(A_56)) | ~m1_subset_1(C_58, u1_struct_0(A_56)) | ~m1_subset_1(B_57, u1_struct_0(A_56)) | ~l1_lattices(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.92/2.79  tff(c_54, plain, (v7_lattices('#skF_8')), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.92/2.79  tff(c_923, plain, (![A_106, B_107, C_108, D_109]: (k2_lattices(A_106, k2_lattices(A_106, B_107, C_108), D_109)=k2_lattices(A_106, B_107, k2_lattices(A_106, C_108, D_109)) | ~m1_subset_1(D_109, u1_struct_0(A_106)) | ~m1_subset_1(C_108, u1_struct_0(A_106)) | ~m1_subset_1(B_107, u1_struct_0(A_106)) | ~v7_lattices(A_106) | ~l1_lattices(A_106) | v2_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.92/2.79  tff(c_945, plain, (![B_107, C_108]: (k2_lattices('#skF_8', k2_lattices('#skF_8', B_107, C_108), '#skF_11')=k2_lattices('#skF_8', B_107, k2_lattices('#skF_8', C_108, '#skF_11')) | ~m1_subset_1(C_108, u1_struct_0('#skF_8')) | ~m1_subset_1(B_107, u1_struct_0('#skF_8')) | ~v7_lattices('#skF_8') | ~l1_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_42, c_923])).
% 7.92/2.79  tff(c_964, plain, (![B_107, C_108]: (k2_lattices('#skF_8', k2_lattices('#skF_8', B_107, C_108), '#skF_11')=k2_lattices('#skF_8', B_107, k2_lattices('#skF_8', C_108, '#skF_11')) | ~m1_subset_1(C_108, u1_struct_0('#skF_8')) | ~m1_subset_1(B_107, u1_struct_0('#skF_8')) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_54, c_945])).
% 7.92/2.79  tff(c_1775, plain, (![B_127, C_128]: (k2_lattices('#skF_8', k2_lattices('#skF_8', B_127, C_128), '#skF_11')=k2_lattices('#skF_8', B_127, k2_lattices('#skF_8', C_128, '#skF_11')) | ~m1_subset_1(C_128, u1_struct_0('#skF_8')) | ~m1_subset_1(B_127, u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_56, c_964])).
% 7.92/2.79  tff(c_2939, plain, (![B_142]: (k2_lattices('#skF_8', k2_lattices('#skF_8', B_142, '#skF_11'), '#skF_11')=k2_lattices('#skF_8', B_142, k2_lattices('#skF_8', '#skF_11', '#skF_11')) | ~m1_subset_1(B_142, u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_42, c_1775])).
% 7.92/2.79  tff(c_3025, plain, (k2_lattices('#skF_8', k2_lattices('#skF_8', '#skF_9', '#skF_11'), '#skF_11')=k2_lattices('#skF_8', '#skF_9', k2_lattices('#skF_8', '#skF_11', '#skF_11'))), inference(resolution, [status(thm)], [c_46, c_2939])).
% 7.92/2.79  tff(c_3043, plain, (m1_subset_1(k2_lattices('#skF_8', '#skF_9', k2_lattices('#skF_8', '#skF_11', '#skF_11')), u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_11', u1_struct_0('#skF_8')) | ~m1_subset_1(k2_lattices('#skF_8', '#skF_9', '#skF_11'), u1_struct_0('#skF_8')) | ~l1_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_3025, c_32])).
% 7.92/2.79  tff(c_3055, plain, (m1_subset_1(k2_lattices('#skF_8', '#skF_9', k2_lattices('#skF_8', '#skF_11', '#skF_11')), u1_struct_0('#skF_8')) | ~m1_subset_1(k2_lattices('#skF_8', '#skF_9', '#skF_11'), u1_struct_0('#skF_8')) | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_42, c_3043])).
% 7.92/2.79  tff(c_3056, plain, (m1_subset_1(k2_lattices('#skF_8', '#skF_9', k2_lattices('#skF_8', '#skF_11', '#skF_11')), u1_struct_0('#skF_8')) | ~m1_subset_1(k2_lattices('#skF_8', '#skF_9', '#skF_11'), u1_struct_0('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_56, c_3055])).
% 7.92/2.79  tff(c_3777, plain, (~m1_subset_1(k2_lattices('#skF_8', '#skF_9', '#skF_11'), u1_struct_0('#skF_8'))), inference(splitLeft, [status(thm)], [c_3056])).
% 7.92/2.79  tff(c_3780, plain, (~m1_subset_1('#skF_11', u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_8')) | ~l1_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_32, c_3777])).
% 7.92/2.79  tff(c_3783, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_46, c_42, c_3780])).
% 7.92/2.79  tff(c_3785, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_3783])).
% 7.92/2.79  tff(c_3787, plain, (m1_subset_1(k2_lattices('#skF_8', '#skF_9', '#skF_11'), u1_struct_0('#skF_8'))), inference(splitRight, [status(thm)], [c_3056])).
% 7.92/2.79  tff(c_77, plain, (![A_85, B_86, C_87]: (r1_lattices(A_85, B_86, C_87) | k1_lattices(A_85, B_86, C_87)!=C_87 | ~m1_subset_1(C_87, u1_struct_0(A_85)) | ~m1_subset_1(B_86, u1_struct_0(A_85)) | ~l2_lattices(A_85) | v2_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.92/2.79  tff(c_7775, plain, (![A_187, B_188, B_189, C_190]: (r1_lattices(A_187, B_188, k2_lattices(A_187, B_189, C_190)) | k1_lattices(A_187, B_188, k2_lattices(A_187, B_189, C_190))!=k2_lattices(A_187, B_189, C_190) | ~m1_subset_1(B_188, u1_struct_0(A_187)) | ~l2_lattices(A_187) | ~m1_subset_1(C_190, u1_struct_0(A_187)) | ~m1_subset_1(B_189, u1_struct_0(A_187)) | ~l1_lattices(A_187) | v2_struct_0(A_187))), inference(resolution, [status(thm)], [c_32, c_77])).
% 7.92/2.79  tff(c_38, plain, (~r1_lattices('#skF_8', k2_lattices('#skF_8', '#skF_9', '#skF_11'), k2_lattices('#skF_8', '#skF_10', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.92/2.79  tff(c_7780, plain, (k1_lattices('#skF_8', k2_lattices('#skF_8', '#skF_9', '#skF_11'), k2_lattices('#skF_8', '#skF_10', '#skF_11'))!=k2_lattices('#skF_8', '#skF_10', '#skF_11') | ~m1_subset_1(k2_lattices('#skF_8', '#skF_9', '#skF_11'), u1_struct_0('#skF_8')) | ~l2_lattices('#skF_8') | ~m1_subset_1('#skF_11', u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_10', u1_struct_0('#skF_8')) | ~l1_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_7775, c_38])).
% 7.92/2.79  tff(c_7952, plain, (k1_lattices('#skF_8', k2_lattices('#skF_8', '#skF_9', '#skF_11'), k2_lattices('#skF_8', '#skF_10', '#skF_11'))!=k2_lattices('#skF_8', '#skF_10', '#skF_11') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_44, c_42, c_61, c_3787, c_7780])).
% 7.92/2.79  tff(c_7953, plain, (k1_lattices('#skF_8', k2_lattices('#skF_8', '#skF_9', '#skF_11'), k2_lattices('#skF_8', '#skF_10', '#skF_11'))!=k2_lattices('#skF_8', '#skF_10', '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_56, c_7952])).
% 7.92/2.79  tff(c_52, plain, (v8_lattices('#skF_8')), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.92/2.79  tff(c_40, plain, (r1_lattices('#skF_8', '#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.92/2.79  tff(c_120, plain, (![A_88, B_89, C_90]: (k1_lattices(A_88, B_89, C_90)=C_90 | ~r1_lattices(A_88, B_89, C_90) | ~m1_subset_1(C_90, u1_struct_0(A_88)) | ~m1_subset_1(B_89, u1_struct_0(A_88)) | ~l2_lattices(A_88) | v2_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.92/2.79  tff(c_122, plain, (k1_lattices('#skF_8', '#skF_9', '#skF_10')='#skF_10' | ~m1_subset_1('#skF_10', u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_8')) | ~l2_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_40, c_120])).
% 7.92/2.79  tff(c_125, plain, (k1_lattices('#skF_8', '#skF_9', '#skF_10')='#skF_10' | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_46, c_44, c_122])).
% 7.92/2.79  tff(c_126, plain, (k1_lattices('#skF_8', '#skF_9', '#skF_10')='#skF_10'), inference(negUnitSimplification, [status(thm)], [c_56, c_125])).
% 7.92/2.79  tff(c_50, plain, (v9_lattices('#skF_8')), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.92/2.79  tff(c_288, plain, (![A_93, B_94, C_95]: (k2_lattices(A_93, B_94, k1_lattices(A_93, B_94, C_95))=B_94 | ~m1_subset_1(C_95, u1_struct_0(A_93)) | ~m1_subset_1(B_94, u1_struct_0(A_93)) | ~v9_lattices(A_93) | ~l3_lattices(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.92/2.79  tff(c_308, plain, (![B_94]: (k2_lattices('#skF_8', B_94, k1_lattices('#skF_8', B_94, '#skF_10'))=B_94 | ~m1_subset_1(B_94, u1_struct_0('#skF_8')) | ~v9_lattices('#skF_8') | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_44, c_288])).
% 7.92/2.79  tff(c_325, plain, (![B_94]: (k2_lattices('#skF_8', B_94, k1_lattices('#skF_8', B_94, '#skF_10'))=B_94 | ~m1_subset_1(B_94, u1_struct_0('#skF_8')) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50, c_308])).
% 7.92/2.79  tff(c_473, plain, (![B_100]: (k2_lattices('#skF_8', B_100, k1_lattices('#skF_8', B_100, '#skF_10'))=B_100 | ~m1_subset_1(B_100, u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_56, c_325])).
% 7.92/2.79  tff(c_499, plain, (k2_lattices('#skF_8', '#skF_9', k1_lattices('#skF_8', '#skF_9', '#skF_10'))='#skF_9'), inference(resolution, [status(thm)], [c_46, c_473])).
% 7.92/2.79  tff(c_537, plain, (k2_lattices('#skF_8', '#skF_9', '#skF_10')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_126, c_499])).
% 7.92/2.79  tff(c_6078, plain, (![B_179]: (k2_lattices('#skF_8', k2_lattices('#skF_8', B_179, '#skF_10'), '#skF_11')=k2_lattices('#skF_8', B_179, k2_lattices('#skF_8', '#skF_10', '#skF_11')) | ~m1_subset_1(B_179, u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_44, c_1775])).
% 7.92/2.79  tff(c_6137, plain, (k2_lattices('#skF_8', k2_lattices('#skF_8', '#skF_9', '#skF_10'), '#skF_11')=k2_lattices('#skF_8', '#skF_9', k2_lattices('#skF_8', '#skF_10', '#skF_11'))), inference(resolution, [status(thm)], [c_46, c_6078])).
% 7.92/2.79  tff(c_6190, plain, (k2_lattices('#skF_8', '#skF_9', k2_lattices('#skF_8', '#skF_10', '#skF_11'))=k2_lattices('#skF_8', '#skF_9', '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_537, c_6137])).
% 7.92/2.79  tff(c_420, plain, (![A_97, B_98, C_99]: (k1_lattices(A_97, k2_lattices(A_97, B_98, C_99), C_99)=C_99 | ~m1_subset_1(C_99, u1_struct_0(A_97)) | ~m1_subset_1(B_98, u1_struct_0(A_97)) | ~v8_lattices(A_97) | ~l3_lattices(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.92/2.79  tff(c_8220, plain, (![A_191, B_192, B_193, C_194]: (k1_lattices(A_191, k2_lattices(A_191, B_192, k2_lattices(A_191, B_193, C_194)), k2_lattices(A_191, B_193, C_194))=k2_lattices(A_191, B_193, C_194) | ~m1_subset_1(B_192, u1_struct_0(A_191)) | ~v8_lattices(A_191) | ~l3_lattices(A_191) | ~m1_subset_1(C_194, u1_struct_0(A_191)) | ~m1_subset_1(B_193, u1_struct_0(A_191)) | ~l1_lattices(A_191) | v2_struct_0(A_191))), inference(resolution, [status(thm)], [c_32, c_420])).
% 7.92/2.79  tff(c_8309, plain, (k1_lattices('#skF_8', k2_lattices('#skF_8', '#skF_9', '#skF_11'), k2_lattices('#skF_8', '#skF_10', '#skF_11'))=k2_lattices('#skF_8', '#skF_10', '#skF_11') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_8')) | ~v8_lattices('#skF_8') | ~l3_lattices('#skF_8') | ~m1_subset_1('#skF_11', u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_10', u1_struct_0('#skF_8')) | ~l1_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_6190, c_8220])).
% 7.92/2.79  tff(c_8697, plain, (k1_lattices('#skF_8', k2_lattices('#skF_8', '#skF_9', '#skF_11'), k2_lattices('#skF_8', '#skF_10', '#skF_11'))=k2_lattices('#skF_8', '#skF_10', '#skF_11') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_44, c_42, c_48, c_52, c_46, c_8309])).
% 7.92/2.79  tff(c_8699, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_7953, c_8697])).
% 7.92/2.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.92/2.79  
% 7.92/2.79  Inference rules
% 7.92/2.79  ----------------------
% 7.92/2.79  #Ref     : 0
% 7.92/2.79  #Sup     : 1793
% 7.92/2.79  #Fact    : 0
% 7.92/2.79  #Define  : 0
% 7.92/2.79  #Split   : 28
% 7.92/2.79  #Chain   : 0
% 7.92/2.79  #Close   : 0
% 7.92/2.79  
% 7.92/2.79  Ordering : KBO
% 7.92/2.79  
% 7.92/2.79  Simplification rules
% 7.92/2.79  ----------------------
% 7.92/2.79  #Subsume      : 95
% 7.92/2.79  #Demod        : 3201
% 7.92/2.79  #Tautology    : 893
% 7.92/2.79  #SimpNegUnit  : 670
% 7.92/2.79  #BackRed      : 37
% 7.92/2.79  
% 7.92/2.79  #Partial instantiations: 0
% 7.92/2.79  #Strategies tried      : 1
% 7.92/2.79  
% 7.92/2.79  Timing (in seconds)
% 7.92/2.79  ----------------------
% 7.92/2.79  Preprocessing        : 0.33
% 7.92/2.79  Parsing              : 0.18
% 7.92/2.79  CNF conversion       : 0.03
% 7.92/2.79  Main loop            : 1.72
% 7.92/2.79  Inferencing          : 0.51
% 7.92/2.79  Reduction            : 0.73
% 7.92/2.79  Demodulation         : 0.56
% 7.92/2.79  BG Simplification    : 0.06
% 7.92/2.79  Subsumption          : 0.33
% 7.92/2.79  Abstraction          : 0.09
% 7.92/2.79  MUC search           : 0.00
% 7.92/2.79  Cooper               : 0.00
% 7.92/2.79  Total                : 2.07
% 7.92/2.79  Index Insertion      : 0.00
% 7.92/2.79  Index Deletion       : 0.00
% 7.92/2.79  Index Matching       : 0.00
% 7.92/2.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
