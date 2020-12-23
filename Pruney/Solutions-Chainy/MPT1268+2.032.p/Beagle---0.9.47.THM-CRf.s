%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:50 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 130 expanded)
%              Number of leaves         :   25 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :  148 ( 388 expanded)
%              Number of equality atoms :   20 (  52 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

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

tff(c_249,plain,(
    ! [B_56,A_57] :
      ( v2_tops_1(B_56,A_57)
      | k1_tops_1(A_57,B_56) != k1_xboole_0
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_256,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_249])).

tff(c_260,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_256])).

tff(c_261,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_260])).

tff(c_147,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(k1_tops_1(A_50,B_51),B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_152,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_147])).

tff(c_156,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_152])).

tff(c_30,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_291,plain,(
    ! [A_60,B_61] :
      ( v3_pre_topc(k1_tops_1(A_60,B_61),A_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_296,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_291])).

tff(c_300,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_296])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | ~ m1_subset_1(A_36,k1_zfmisc_1(B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_64,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_56])).

tff(c_91,plain,(
    ! [A_41,C_42,B_43] :
      ( r1_tarski(A_41,C_42)
      | ~ r1_tarski(B_43,C_42)
      | ~ r1_tarski(A_41,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_114,plain,(
    ! [A_46] :
      ( r1_tarski(A_46,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_46,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_64,c_91])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_119,plain,(
    ! [A_3,A_46] :
      ( r1_tarski(A_3,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_3,A_46)
      | ~ r1_tarski(A_46,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_114,c_8])).

tff(c_170,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_156,c_119])).

tff(c_177,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_170])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_50,plain,(
    ! [C_31] :
      ( v2_tops_1('#skF_2','#skF_1')
      | k1_xboole_0 = C_31
      | ~ v3_pre_topc(C_31,'#skF_1')
      | ~ r1_tarski(C_31,'#skF_2')
      | ~ m1_subset_1(C_31,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_278,plain,(
    ! [C_59] :
      ( k1_xboole_0 = C_59
      | ~ v3_pre_topc(C_59,'#skF_1')
      | ~ r1_tarski(C_59,'#skF_2')
      | ~ m1_subset_1(C_59,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_50])).

tff(c_485,plain,(
    ! [A_72] :
      ( k1_xboole_0 = A_72
      | ~ v3_pre_topc(A_72,'#skF_1')
      | ~ r1_tarski(A_72,'#skF_2')
      | ~ r1_tarski(A_72,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_14,c_278])).

tff(c_498,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_177,c_485])).

tff(c_521,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_300,c_498])).

tff(c_523,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_261,c_521])).

tff(c_524,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_525,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_34,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_527,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_34])).

tff(c_36,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_529,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_36])).

tff(c_38,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_557,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_38])).

tff(c_835,plain,(
    ! [A_100,B_101] :
      ( k1_tops_1(A_100,B_101) = k1_xboole_0
      | ~ v2_tops_1(B_101,A_100)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_845,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_835])).

tff(c_852,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_525,c_845])).

tff(c_1062,plain,(
    ! [B_112,A_113,C_114] :
      ( r1_tarski(B_112,k1_tops_1(A_113,C_114))
      | ~ r1_tarski(B_112,C_114)
      | ~ v3_pre_topc(B_112,A_113)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1069,plain,(
    ! [B_112] :
      ( r1_tarski(B_112,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_112,'#skF_2')
      | ~ v3_pre_topc(B_112,'#skF_1')
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_1062])).

tff(c_1171,plain,(
    ! [B_122] :
      ( r1_tarski(B_122,k1_xboole_0)
      | ~ r1_tarski(B_122,'#skF_2')
      | ~ v3_pre_topc(B_122,'#skF_1')
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_852,c_1069])).

tff(c_1174,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_557,c_1171])).

tff(c_1184,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_527,c_529,c_1174])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_540,plain,(
    ! [B_77,A_78] :
      ( B_77 = A_78
      | ~ r1_tarski(B_77,A_78)
      | ~ r1_tarski(A_78,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_555,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_540])).

tff(c_1202,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1184,c_555])).

tff(c_1219,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_524,c_1202])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:36:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.04/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.47  
% 3.04/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.47  %$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.04/1.47  
% 3.04/1.47  %Foreground sorts:
% 3.04/1.47  
% 3.04/1.47  
% 3.04/1.47  %Background operators:
% 3.04/1.47  
% 3.04/1.47  
% 3.04/1.47  %Foreground operators:
% 3.04/1.47  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.04/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.04/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.04/1.47  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.04/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.04/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.04/1.47  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.04/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.04/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.04/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.04/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.04/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.04/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.04/1.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.04/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.04/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.04/1.47  
% 3.21/1.48  tff(f_100, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 3.21/1.48  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 3.21/1.48  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 3.21/1.48  tff(f_51, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.21/1.48  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.21/1.48  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.21/1.48  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.21/1.48  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 3.21/1.48  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.21/1.48  tff(c_32, plain, (k1_xboole_0!='#skF_3' | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.21/1.48  tff(c_54, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_32])).
% 3.21/1.48  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.21/1.48  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.21/1.48  tff(c_249, plain, (![B_56, A_57]: (v2_tops_1(B_56, A_57) | k1_tops_1(A_57, B_56)!=k1_xboole_0 | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.21/1.48  tff(c_256, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_249])).
% 3.21/1.48  tff(c_260, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_256])).
% 3.21/1.48  tff(c_261, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_54, c_260])).
% 3.21/1.48  tff(c_147, plain, (![A_50, B_51]: (r1_tarski(k1_tops_1(A_50, B_51), B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.21/1.48  tff(c_152, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_147])).
% 3.21/1.48  tff(c_156, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_152])).
% 3.21/1.48  tff(c_30, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.21/1.48  tff(c_291, plain, (![A_60, B_61]: (v3_pre_topc(k1_tops_1(A_60, B_61), A_60) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.21/1.48  tff(c_296, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_291])).
% 3.21/1.48  tff(c_300, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_296])).
% 3.21/1.48  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.21/1.48  tff(c_56, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | ~m1_subset_1(A_36, k1_zfmisc_1(B_37)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.21/1.48  tff(c_64, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_56])).
% 3.21/1.48  tff(c_91, plain, (![A_41, C_42, B_43]: (r1_tarski(A_41, C_42) | ~r1_tarski(B_43, C_42) | ~r1_tarski(A_41, B_43))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.21/1.48  tff(c_114, plain, (![A_46]: (r1_tarski(A_46, u1_struct_0('#skF_1')) | ~r1_tarski(A_46, '#skF_2'))), inference(resolution, [status(thm)], [c_64, c_91])).
% 3.21/1.48  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.21/1.48  tff(c_119, plain, (![A_3, A_46]: (r1_tarski(A_3, u1_struct_0('#skF_1')) | ~r1_tarski(A_3, A_46) | ~r1_tarski(A_46, '#skF_2'))), inference(resolution, [status(thm)], [c_114, c_8])).
% 3.21/1.48  tff(c_170, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1')) | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_156, c_119])).
% 3.21/1.48  tff(c_177, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_170])).
% 3.21/1.48  tff(c_14, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.21/1.48  tff(c_50, plain, (![C_31]: (v2_tops_1('#skF_2', '#skF_1') | k1_xboole_0=C_31 | ~v3_pre_topc(C_31, '#skF_1') | ~r1_tarski(C_31, '#skF_2') | ~m1_subset_1(C_31, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.21/1.48  tff(c_278, plain, (![C_59]: (k1_xboole_0=C_59 | ~v3_pre_topc(C_59, '#skF_1') | ~r1_tarski(C_59, '#skF_2') | ~m1_subset_1(C_59, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_50])).
% 3.21/1.48  tff(c_485, plain, (![A_72]: (k1_xboole_0=A_72 | ~v3_pre_topc(A_72, '#skF_1') | ~r1_tarski(A_72, '#skF_2') | ~r1_tarski(A_72, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_14, c_278])).
% 3.21/1.48  tff(c_498, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_177, c_485])).
% 3.21/1.48  tff(c_521, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_156, c_300, c_498])).
% 3.21/1.48  tff(c_523, plain, $false, inference(negUnitSimplification, [status(thm)], [c_261, c_521])).
% 3.21/1.48  tff(c_524, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_32])).
% 3.21/1.48  tff(c_525, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_32])).
% 3.21/1.48  tff(c_34, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.21/1.48  tff(c_527, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_525, c_34])).
% 3.21/1.48  tff(c_36, plain, (r1_tarski('#skF_3', '#skF_2') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.21/1.48  tff(c_529, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_525, c_36])).
% 3.21/1.48  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.21/1.48  tff(c_557, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_525, c_38])).
% 3.21/1.48  tff(c_835, plain, (![A_100, B_101]: (k1_tops_1(A_100, B_101)=k1_xboole_0 | ~v2_tops_1(B_101, A_100) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.21/1.48  tff(c_845, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_835])).
% 3.21/1.48  tff(c_852, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_525, c_845])).
% 3.21/1.48  tff(c_1062, plain, (![B_112, A_113, C_114]: (r1_tarski(B_112, k1_tops_1(A_113, C_114)) | ~r1_tarski(B_112, C_114) | ~v3_pre_topc(B_112, A_113) | ~m1_subset_1(C_114, k1_zfmisc_1(u1_struct_0(A_113))) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_pre_topc(A_113))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.21/1.48  tff(c_1069, plain, (![B_112]: (r1_tarski(B_112, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_112, '#skF_2') | ~v3_pre_topc(B_112, '#skF_1') | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_1062])).
% 3.21/1.48  tff(c_1171, plain, (![B_122]: (r1_tarski(B_122, k1_xboole_0) | ~r1_tarski(B_122, '#skF_2') | ~v3_pre_topc(B_122, '#skF_1') | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_852, c_1069])).
% 3.21/1.48  tff(c_1174, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_557, c_1171])).
% 3.21/1.48  tff(c_1184, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_527, c_529, c_1174])).
% 3.21/1.48  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.21/1.48  tff(c_540, plain, (![B_77, A_78]: (B_77=A_78 | ~r1_tarski(B_77, A_78) | ~r1_tarski(A_78, B_77))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.21/1.48  tff(c_555, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_540])).
% 3.21/1.48  tff(c_1202, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1184, c_555])).
% 3.21/1.48  tff(c_1219, plain, $false, inference(negUnitSimplification, [status(thm)], [c_524, c_1202])).
% 3.21/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.48  
% 3.21/1.48  Inference rules
% 3.21/1.48  ----------------------
% 3.21/1.48  #Ref     : 0
% 3.21/1.48  #Sup     : 256
% 3.21/1.48  #Fact    : 0
% 3.21/1.48  #Define  : 0
% 3.21/1.48  #Split   : 13
% 3.21/1.48  #Chain   : 0
% 3.21/1.48  #Close   : 0
% 3.21/1.48  
% 3.21/1.48  Ordering : KBO
% 3.21/1.48  
% 3.21/1.48  Simplification rules
% 3.21/1.48  ----------------------
% 3.21/1.48  #Subsume      : 100
% 3.21/1.48  #Demod        : 136
% 3.21/1.48  #Tautology    : 59
% 3.21/1.48  #SimpNegUnit  : 7
% 3.21/1.49  #BackRed      : 4
% 3.21/1.49  
% 3.21/1.49  #Partial instantiations: 0
% 3.21/1.49  #Strategies tried      : 1
% 3.21/1.49  
% 3.21/1.49  Timing (in seconds)
% 3.21/1.49  ----------------------
% 3.21/1.49  Preprocessing        : 0.30
% 3.21/1.49  Parsing              : 0.16
% 3.21/1.49  CNF conversion       : 0.02
% 3.21/1.49  Main loop            : 0.40
% 3.21/1.49  Inferencing          : 0.14
% 3.21/1.49  Reduction            : 0.13
% 3.21/1.49  Demodulation         : 0.09
% 3.21/1.49  BG Simplification    : 0.02
% 3.21/1.49  Subsumption          : 0.09
% 3.21/1.49  Abstraction          : 0.02
% 3.21/1.49  MUC search           : 0.00
% 3.21/1.49  Cooper               : 0.00
% 3.21/1.49  Total                : 0.74
% 3.21/1.49  Index Insertion      : 0.00
% 3.21/1.49  Index Deletion       : 0.00
% 3.21/1.49  Index Matching       : 0.00
% 3.21/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
