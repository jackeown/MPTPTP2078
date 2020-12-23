%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1717+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:17 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 121 expanded)
%              Number of leaves         :   19 (  52 expanded)
%              Depth                    :   14
%              Number of atoms          :  125 ( 449 expanded)
%              Number of equality atoms :   10 (  59 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tsep_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_tsep_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_tsep_1,type,(
    k2_tsep_1: ( $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => k2_tsep_1(A,B,B) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tmap_1)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_100,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( ~ r1_tsep_1(B,C)
               => ( ( m1_pre_topc(B,C)
                   => k2_tsep_1(A,B,C) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) )
                  & ( k2_tsep_1(A,B,C) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                   => m1_pre_topc(B,C) )
                  & ( m1_pre_topc(C,B)
                   => k2_tsep_1(A,B,C) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) )
                  & ( k2_tsep_1(A,B,C) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C))
                   => m1_pre_topc(C,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tsep_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( m1_pre_topc(B,C)
               => ( ~ r1_tsep_1(B,C)
                  & ~ r1_tsep_1(C,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tmap_1)).

tff(c_28,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_26,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_20,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_30,plain,(
    ! [B_21,A_22] :
      ( l1_pre_topc(B_21)
      | ~ m1_pre_topc(B_21,A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_30])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_36])).

tff(c_8,plain,(
    ! [A_11] :
      ( m1_pre_topc(A_11,A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_22,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_43,plain,(
    ! [A_29,B_30,C_31] :
      ( k2_tsep_1(A_29,B_30,C_31) = g1_pre_topc(u1_struct_0(B_30),u1_pre_topc(B_30))
      | ~ m1_pre_topc(B_30,C_31)
      | r1_tsep_1(B_30,C_31)
      | ~ m1_pre_topc(C_31,A_29)
      | v2_struct_0(C_31)
      | ~ m1_pre_topc(B_30,A_29)
      | v2_struct_0(B_30)
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_47,plain,(
    ! [B_30] :
      ( g1_pre_topc(u1_struct_0(B_30),u1_pre_topc(B_30)) = k2_tsep_1('#skF_1',B_30,'#skF_2')
      | ~ m1_pre_topc(B_30,'#skF_2')
      | r1_tsep_1(B_30,'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_30,'#skF_1')
      | v2_struct_0(B_30)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_20,c_43])).

tff(c_51,plain,(
    ! [B_30] :
      ( g1_pre_topc(u1_struct_0(B_30),u1_pre_topc(B_30)) = k2_tsep_1('#skF_1',B_30,'#skF_2')
      | ~ m1_pre_topc(B_30,'#skF_2')
      | r1_tsep_1(B_30,'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_30,'#skF_1')
      | v2_struct_0(B_30)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_47])).

tff(c_53,plain,(
    ! [B_32] :
      ( g1_pre_topc(u1_struct_0(B_32),u1_pre_topc(B_32)) = k2_tsep_1('#skF_1',B_32,'#skF_2')
      | ~ m1_pre_topc(B_32,'#skF_2')
      | r1_tsep_1(B_32,'#skF_2')
      | ~ m1_pre_topc(B_32,'#skF_1')
      | v2_struct_0(B_32) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_22,c_51])).

tff(c_18,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k2_tsep_1('#skF_1','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_59,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_2')
    | r1_tsep_1('#skF_2','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_18])).

tff(c_66,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_2')
    | r1_tsep_1('#skF_2','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_59])).

tff(c_67,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_2')
    | r1_tsep_1('#skF_2','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_66])).

tff(c_69,plain,(
    ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_72,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_69])).

tff(c_76,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_72])).

tff(c_78,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_77,plain,(
    r1_tsep_1('#skF_2','#skF_2') ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_4,plain,(
    ! [C_10,B_8,A_4] :
      ( ~ r1_tsep_1(C_10,B_8)
      | ~ m1_pre_topc(B_8,C_10)
      | ~ m1_pre_topc(C_10,A_4)
      | v2_struct_0(C_10)
      | ~ m1_pre_topc(B_8,A_4)
      | v2_struct_0(B_8)
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_85,plain,(
    ! [A_4] :
      ( ~ m1_pre_topc('#skF_2','#skF_2')
      | ~ m1_pre_topc('#skF_2',A_4)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4)
      | v2_struct_0(A_4) ) ),
    inference(resolution,[status(thm)],[c_77,c_4])).

tff(c_91,plain,(
    ! [A_4] :
      ( ~ m1_pre_topc('#skF_2','#skF_2')
      | ~ m1_pre_topc('#skF_2',A_4)
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4)
      | v2_struct_0(A_4) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_22,c_85])).

tff(c_106,plain,(
    ! [A_36] :
      ( ~ m1_pre_topc('#skF_2',A_36)
      | ~ l1_pre_topc(A_36)
      | ~ v2_pre_topc(A_36)
      | v2_struct_0(A_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_91])).

tff(c_116,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_106])).

tff(c_127,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_116])).

tff(c_129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_127])).

%------------------------------------------------------------------------------
