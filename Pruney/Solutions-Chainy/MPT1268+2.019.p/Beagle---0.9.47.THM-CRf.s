%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:49 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 133 expanded)
%              Number of leaves         :   26 (  55 expanded)
%              Depth                    :    8
%              Number of atoms          :  143 ( 406 expanded)
%              Number of equality atoms :   25 (  64 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r1_tarski(C,B)
                      & v3_pre_topc(C,A) )
                   => C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

tff(c_32,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_54,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_333,plain,(
    ! [B_61,A_62] :
      ( v2_tops_1(B_61,A_62)
      | k1_tops_1(A_62,B_61) != k1_xboole_0
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_339,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_333])).

tff(c_343,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_339])).

tff(c_344,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_343])).

tff(c_268,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(k1_tops_1(A_56,B_57),B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_270,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_268])).

tff(c_273,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_270])).

tff(c_30,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_357,plain,(
    ! [A_65,B_66] :
      ( v3_pre_topc(k1_tops_1(A_65,B_66),A_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_361,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_357])).

tff(c_365,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_361])).

tff(c_322,plain,(
    ! [A_59,B_60] :
      ( m1_subset_1(k1_tops_1(A_59,B_60),k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_50,plain,(
    ! [C_31] :
      ( v2_tops_1('#skF_2','#skF_1')
      | k1_xboole_0 = C_31
      | ~ v3_pre_topc(C_31,'#skF_1')
      | ~ r1_tarski(C_31,'#skF_2')
      | ~ m1_subset_1(C_31,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_309,plain,(
    ! [C_31] :
      ( k1_xboole_0 = C_31
      | ~ v3_pre_topc(C_31,'#skF_1')
      | ~ r1_tarski(C_31,'#skF_2')
      | ~ m1_subset_1(C_31,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_50])).

tff(c_326,plain,(
    ! [B_60] :
      ( k1_tops_1('#skF_1',B_60) = k1_xboole_0
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_60),'#skF_1')
      | ~ r1_tarski(k1_tops_1('#skF_1',B_60),'#skF_2')
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_322,c_309])).

tff(c_416,plain,(
    ! [B_77] :
      ( k1_tops_1('#skF_1',B_77) = k1_xboole_0
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_77),'#skF_1')
      | ~ r1_tarski(k1_tops_1('#skF_1',B_77),'#skF_2')
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_326])).

tff(c_423,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_416])).

tff(c_429,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_365,c_423])).

tff(c_431,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_344,c_429])).

tff(c_432,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_433,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_36,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_435,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_36])).

tff(c_438,plain,(
    ! [A_78,B_79] :
      ( k4_xboole_0(A_78,B_79) = k1_xboole_0
      | ~ r1_tarski(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_448,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_435,c_438])).

tff(c_12,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_544,plain,(
    ! [B_87,A_88] :
      ( B_87 = A_88
      | ~ r1_tarski(B_87,A_88)
      | ~ r1_tarski(A_88,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_692,plain,(
    ! [A_95,B_96] :
      ( k4_xboole_0(A_95,B_96) = A_95
      | ~ r1_tarski(A_95,k4_xboole_0(A_95,B_96)) ) ),
    inference(resolution,[status(thm)],[c_12,c_544])).

tff(c_718,plain,
    ( k4_xboole_0('#skF_3','#skF_2') = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_448,c_692])).

tff(c_728,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_718])).

tff(c_729,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_432,c_728])).

tff(c_34,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_437,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_34])).

tff(c_38,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_543,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_38])).

tff(c_734,plain,(
    ! [A_97,B_98] :
      ( k1_tops_1(A_97,B_98) = k1_xboole_0
      | ~ v2_tops_1(B_98,A_97)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_740,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_734])).

tff(c_746,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_433,c_740])).

tff(c_928,plain,(
    ! [B_111,A_112,C_113] :
      ( r1_tarski(B_111,k1_tops_1(A_112,C_113))
      | ~ r1_tarski(B_111,C_113)
      | ~ v3_pre_topc(B_111,A_112)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_936,plain,(
    ! [B_111] :
      ( r1_tarski(B_111,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_111,'#skF_2')
      | ~ v3_pre_topc(B_111,'#skF_1')
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_928])).

tff(c_947,plain,(
    ! [B_114] :
      ( r1_tarski(B_114,k1_xboole_0)
      | ~ r1_tarski(B_114,'#skF_2')
      | ~ v3_pre_topc(B_114,'#skF_1')
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_746,c_936])).

tff(c_957,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_543,c_947])).

tff(c_969,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_435,c_957])).

tff(c_971,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_729,c_969])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:32:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.43  
% 2.70/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.43  %$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.70/1.43  
% 2.70/1.43  %Foreground sorts:
% 2.70/1.43  
% 2.70/1.43  
% 2.70/1.43  %Background operators:
% 2.70/1.43  
% 2.70/1.43  
% 2.70/1.43  %Foreground operators:
% 2.70/1.43  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.70/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.70/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.70/1.43  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 2.70/1.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.70/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.70/1.43  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.70/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.70/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.70/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.70/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.70/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.43  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.70/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.70/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.70/1.43  
% 2.70/1.45  tff(f_100, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tops_1)).
% 2.70/1.45  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 2.70/1.45  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 2.70/1.45  tff(f_51, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 2.70/1.45  tff(f_43, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 2.70/1.45  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.70/1.45  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.70/1.45  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.70/1.45  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_1)).
% 2.70/1.45  tff(c_32, plain, (k1_xboole_0!='#skF_3' | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.70/1.45  tff(c_54, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_32])).
% 2.70/1.45  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.70/1.45  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.70/1.45  tff(c_333, plain, (![B_61, A_62]: (v2_tops_1(B_61, A_62) | k1_tops_1(A_62, B_61)!=k1_xboole_0 | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.70/1.45  tff(c_339, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_333])).
% 2.70/1.45  tff(c_343, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_339])).
% 2.70/1.45  tff(c_344, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_54, c_343])).
% 2.70/1.45  tff(c_268, plain, (![A_56, B_57]: (r1_tarski(k1_tops_1(A_56, B_57), B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.70/1.45  tff(c_270, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_268])).
% 2.70/1.45  tff(c_273, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_270])).
% 2.70/1.45  tff(c_30, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.70/1.45  tff(c_357, plain, (![A_65, B_66]: (v3_pre_topc(k1_tops_1(A_65, B_66), A_65) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.70/1.45  tff(c_361, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_357])).
% 2.70/1.45  tff(c_365, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_361])).
% 2.70/1.45  tff(c_322, plain, (![A_59, B_60]: (m1_subset_1(k1_tops_1(A_59, B_60), k1_zfmisc_1(u1_struct_0(A_59))) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.70/1.45  tff(c_50, plain, (![C_31]: (v2_tops_1('#skF_2', '#skF_1') | k1_xboole_0=C_31 | ~v3_pre_topc(C_31, '#skF_1') | ~r1_tarski(C_31, '#skF_2') | ~m1_subset_1(C_31, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.70/1.45  tff(c_309, plain, (![C_31]: (k1_xboole_0=C_31 | ~v3_pre_topc(C_31, '#skF_1') | ~r1_tarski(C_31, '#skF_2') | ~m1_subset_1(C_31, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_50])).
% 2.70/1.45  tff(c_326, plain, (![B_60]: (k1_tops_1('#skF_1', B_60)=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', B_60), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', B_60), '#skF_2') | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_322, c_309])).
% 2.70/1.45  tff(c_416, plain, (![B_77]: (k1_tops_1('#skF_1', B_77)=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', B_77), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', B_77), '#skF_2') | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_326])).
% 2.70/1.45  tff(c_423, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_26, c_416])).
% 2.70/1.45  tff(c_429, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_273, c_365, c_423])).
% 2.70/1.45  tff(c_431, plain, $false, inference(negUnitSimplification, [status(thm)], [c_344, c_429])).
% 2.70/1.45  tff(c_432, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_32])).
% 2.70/1.45  tff(c_433, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_32])).
% 2.70/1.45  tff(c_36, plain, (r1_tarski('#skF_3', '#skF_2') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.70/1.45  tff(c_435, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_433, c_36])).
% 2.70/1.45  tff(c_438, plain, (![A_78, B_79]: (k4_xboole_0(A_78, B_79)=k1_xboole_0 | ~r1_tarski(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.70/1.45  tff(c_448, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_435, c_438])).
% 2.70/1.45  tff(c_12, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.70/1.45  tff(c_544, plain, (![B_87, A_88]: (B_87=A_88 | ~r1_tarski(B_87, A_88) | ~r1_tarski(A_88, B_87))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.70/1.45  tff(c_692, plain, (![A_95, B_96]: (k4_xboole_0(A_95, B_96)=A_95 | ~r1_tarski(A_95, k4_xboole_0(A_95, B_96)))), inference(resolution, [status(thm)], [c_12, c_544])).
% 2.70/1.45  tff(c_718, plain, (k4_xboole_0('#skF_3', '#skF_2')='#skF_3' | ~r1_tarski('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_448, c_692])).
% 2.70/1.45  tff(c_728, plain, (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_448, c_718])).
% 2.70/1.45  tff(c_729, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_432, c_728])).
% 2.70/1.45  tff(c_34, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.70/1.45  tff(c_437, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_433, c_34])).
% 2.70/1.45  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.70/1.45  tff(c_543, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_433, c_38])).
% 2.70/1.45  tff(c_734, plain, (![A_97, B_98]: (k1_tops_1(A_97, B_98)=k1_xboole_0 | ~v2_tops_1(B_98, A_97) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.70/1.45  tff(c_740, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_734])).
% 2.70/1.45  tff(c_746, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_433, c_740])).
% 2.70/1.45  tff(c_928, plain, (![B_111, A_112, C_113]: (r1_tarski(B_111, k1_tops_1(A_112, C_113)) | ~r1_tarski(B_111, C_113) | ~v3_pre_topc(B_111, A_112) | ~m1_subset_1(C_113, k1_zfmisc_1(u1_struct_0(A_112))) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.70/1.45  tff(c_936, plain, (![B_111]: (r1_tarski(B_111, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_111, '#skF_2') | ~v3_pre_topc(B_111, '#skF_1') | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_928])).
% 2.70/1.45  tff(c_947, plain, (![B_114]: (r1_tarski(B_114, k1_xboole_0) | ~r1_tarski(B_114, '#skF_2') | ~v3_pre_topc(B_114, '#skF_1') | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_746, c_936])).
% 2.70/1.45  tff(c_957, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_543, c_947])).
% 2.70/1.45  tff(c_969, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_437, c_435, c_957])).
% 2.70/1.45  tff(c_971, plain, $false, inference(negUnitSimplification, [status(thm)], [c_729, c_969])).
% 2.70/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.45  
% 2.70/1.45  Inference rules
% 2.70/1.45  ----------------------
% 2.70/1.45  #Ref     : 0
% 2.70/1.45  #Sup     : 198
% 2.70/1.45  #Fact    : 0
% 2.70/1.45  #Define  : 0
% 2.70/1.45  #Split   : 8
% 2.70/1.45  #Chain   : 0
% 2.70/1.45  #Close   : 0
% 2.70/1.45  
% 2.70/1.45  Ordering : KBO
% 2.70/1.45  
% 2.70/1.45  Simplification rules
% 2.70/1.45  ----------------------
% 2.70/1.45  #Subsume      : 38
% 2.70/1.45  #Demod        : 145
% 2.70/1.45  #Tautology    : 104
% 2.70/1.45  #SimpNegUnit  : 8
% 2.70/1.45  #BackRed      : 3
% 2.70/1.45  
% 2.70/1.45  #Partial instantiations: 0
% 2.70/1.45  #Strategies tried      : 1
% 2.70/1.45  
% 2.70/1.45  Timing (in seconds)
% 2.70/1.45  ----------------------
% 2.70/1.45  Preprocessing        : 0.30
% 2.70/1.45  Parsing              : 0.16
% 2.70/1.45  CNF conversion       : 0.02
% 2.70/1.45  Main loop            : 0.35
% 2.70/1.45  Inferencing          : 0.12
% 2.70/1.45  Reduction            : 0.11
% 2.70/1.45  Demodulation         : 0.08
% 2.70/1.45  BG Simplification    : 0.02
% 2.70/1.45  Subsumption          : 0.07
% 2.70/1.45  Abstraction          : 0.02
% 2.70/1.45  MUC search           : 0.00
% 2.70/1.45  Cooper               : 0.00
% 2.70/1.45  Total                : 0.69
% 2.70/1.45  Index Insertion      : 0.00
% 2.70/1.45  Index Deletion       : 0.00
% 2.70/1.45  Index Matching       : 0.00
% 2.70/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
