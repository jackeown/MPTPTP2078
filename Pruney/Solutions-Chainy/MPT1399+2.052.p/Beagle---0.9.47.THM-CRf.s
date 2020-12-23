%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:25 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 264 expanded)
%              Number of leaves         :   41 ( 105 expanded)
%              Depth                    :   12
%              Number of atoms          :  177 ( 773 expanded)
%              Number of equality atoms :   27 (  98 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_160,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ~ ( ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ( r2_hidden(D,C)
                        <=> ( v3_pre_topc(D,A)
                            & v4_pre_topc(D,A)
                            & r2_hidden(B,D) ) ) )
                    & C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_95,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_109,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_30,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_32,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_40,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_56,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ! [C] :
              ( m1_subset_1(C,A)
             => ( ~ r2_hidden(C,B)
               => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_115,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_34,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_132,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v3_pre_topc(B,A)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_tops_1)).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_54,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_52,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_46,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_75,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2])).

tff(c_28,plain,(
    ! [A_24] :
      ( r2_hidden('#skF_1'(A_24),A_24)
      | k1_xboole_0 = A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_65,plain,(
    ! [A_24] :
      ( r2_hidden('#skF_1'(A_24),A_24)
      | A_24 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_28])).

tff(c_34,plain,(
    ! [A_48] :
      ( v4_pre_topc(k2_struct_0(A_48),A_48)
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_32,plain,(
    ! [A_47] :
      ( l1_struct_0(A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_109,plain,(
    ! [A_71] :
      ( u1_struct_0(A_71) = k2_struct_0(A_71)
      | ~ l1_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_120,plain,(
    ! [A_75] :
      ( u1_struct_0(A_75) = k2_struct_0(A_75)
      | ~ l1_pre_topc(A_75) ) ),
    inference(resolution,[status(thm)],[c_32,c_109])).

tff(c_124,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_120])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_125,plain,(
    m1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_50])).

tff(c_16,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_68,plain,(
    ! [A_8] : m1_subset_1('#skF_5',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_16])).

tff(c_152,plain,(
    ! [C_80,B_81,A_82] :
      ( ~ v1_xboole_0(C_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(C_80))
      | ~ r2_hidden(A_82,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_158,plain,(
    ! [A_8,A_82] :
      ( ~ v1_xboole_0(A_8)
      | ~ r2_hidden(A_82,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_68,c_152])).

tff(c_170,plain,(
    ! [A_82] : ~ r2_hidden(A_82,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_6,plain,(
    ! [A_2] : k1_subset_1(A_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_72,plain,(
    ! [A_2] : k1_subset_1(A_2) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6])).

tff(c_8,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_subset_1(A_7)) = k2_subset_1(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_70,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_subset_1(A_7)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14])).

tff(c_73,plain,(
    ! [A_7] : k3_subset_1(A_7,'#skF_5') = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70])).

tff(c_18,plain,(
    ! [C_15,A_9,B_13] :
      ( r2_hidden(C_15,k3_subset_1(A_9,B_13))
      | r2_hidden(C_15,B_13)
      | ~ m1_subset_1(C_15,A_9)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_9))
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_361,plain,(
    ! [C_106,A_107,B_108] :
      ( r2_hidden(C_106,k3_subset_1(A_107,B_108))
      | r2_hidden(C_106,B_108)
      | ~ m1_subset_1(C_106,A_107)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(A_107))
      | A_107 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_18])).

tff(c_376,plain,(
    ! [C_106,A_7] :
      ( r2_hidden(C_106,A_7)
      | r2_hidden(C_106,'#skF_5')
      | ~ m1_subset_1(C_106,A_7)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_7))
      | A_7 = '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_361])).

tff(c_384,plain,(
    ! [C_106,A_7] :
      ( r2_hidden(C_106,A_7)
      | r2_hidden(C_106,'#skF_5')
      | ~ m1_subset_1(C_106,A_7)
      | A_7 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_376])).

tff(c_385,plain,(
    ! [C_106,A_7] :
      ( r2_hidden(C_106,A_7)
      | ~ m1_subset_1(C_106,A_7)
      | A_7 = '#skF_5' ) ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_384])).

tff(c_36,plain,(
    ! [A_49] :
      ( v3_pre_topc(k2_struct_0(A_49),A_49)
      | ~ l1_pre_topc(A_49)
      | ~ v2_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_71,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_58,plain,(
    ! [D_63] :
      ( r2_hidden(D_63,'#skF_5')
      | ~ r2_hidden('#skF_4',D_63)
      | ~ v4_pre_topc(D_63,'#skF_3')
      | ~ v3_pre_topc(D_63,'#skF_3')
      | ~ m1_subset_1(D_63,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_299,plain,(
    ! [D_63] :
      ( r2_hidden(D_63,'#skF_5')
      | ~ r2_hidden('#skF_4',D_63)
      | ~ v4_pre_topc(D_63,'#skF_3')
      | ~ v3_pre_topc(D_63,'#skF_3')
      | ~ m1_subset_1(D_63,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_58])).

tff(c_301,plain,(
    ! [D_104] :
      ( ~ r2_hidden('#skF_4',D_104)
      | ~ v4_pre_topc(D_104,'#skF_3')
      | ~ v3_pre_topc(D_104,'#skF_3')
      | ~ m1_subset_1(D_104,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_299])).

tff(c_319,plain,
    ( ~ r2_hidden('#skF_4',k2_struct_0('#skF_3'))
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_301])).

tff(c_445,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_319])).

tff(c_448,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_445])).

tff(c_452,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_448])).

tff(c_453,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ r2_hidden('#skF_4',k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_319])).

tff(c_466,plain,(
    ~ r2_hidden('#skF_4',k2_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_453])).

tff(c_469,plain,
    ( ~ m1_subset_1('#skF_4',k2_struct_0('#skF_3'))
    | k2_struct_0('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_385,c_466])).

tff(c_472,plain,(
    k2_struct_0('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_469])).

tff(c_273,plain,(
    ! [A_103] :
      ( m1_subset_1('#skF_2'(A_103),k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103)
      | ~ v2_pre_topc(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_282,plain,
    ( m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_273])).

tff(c_287,plain,
    ( m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_282])).

tff(c_288,plain,(
    m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_287])).

tff(c_22,plain,(
    ! [C_21,B_20,A_19] :
      ( ~ v1_xboole_0(C_21)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(C_21))
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_297,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ r2_hidden(A_19,'#skF_2'('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_288,c_22])).

tff(c_298,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_297])).

tff(c_480,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_472,c_298])).

tff(c_486,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_480])).

tff(c_487,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_453])).

tff(c_492,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_487])).

tff(c_496,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_492])).

tff(c_550,plain,(
    ! [A_123] : ~ r2_hidden(A_123,'#skF_2'('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_297])).

tff(c_555,plain,(
    '#skF_2'('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_65,c_550])).

tff(c_42,plain,(
    ! [A_50] :
      ( ~ v1_xboole_0('#skF_2'(A_50))
      | ~ l1_pre_topc(A_50)
      | ~ v2_pre_topc(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_586,plain,
    ( ~ v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_555,c_42])).

tff(c_599,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_75,c_586])).

tff(c_601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_599])).

tff(c_602,plain,(
    ! [A_8] : ~ v1_xboole_0(A_8) ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_604,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_602,c_75])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:45:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.48  
% 3.11/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.48  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 3.11/1.48  
% 3.11/1.48  %Foreground sorts:
% 3.11/1.48  
% 3.11/1.48  
% 3.11/1.48  %Background operators:
% 3.11/1.48  
% 3.11/1.48  
% 3.11/1.48  %Foreground operators:
% 3.11/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.11/1.48  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.11/1.48  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.11/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.11/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.11/1.48  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.11/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.11/1.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.11/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.11/1.48  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.11/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.11/1.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.11/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.11/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.11/1.48  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.11/1.48  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.11/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.11/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.11/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.11/1.48  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.11/1.48  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.11/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.11/1.48  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.11/1.48  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.11/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.11/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.11/1.48  
% 3.11/1.50  tff(f_160, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_connsp_2)).
% 3.11/1.50  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.11/1.50  tff(f_95, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 3.11/1.50  tff(f_109, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_pre_topc)).
% 3.11/1.50  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.11/1.50  tff(f_99, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.11/1.50  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.11/1.50  tff(f_69, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.11/1.50  tff(f_30, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 3.11/1.50  tff(f_32, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.11/1.50  tff(f_40, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 3.11/1.50  tff(f_56, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_subset_1)).
% 3.11/1.50  tff(f_115, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 3.11/1.50  tff(f_34, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.11/1.50  tff(f_132, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: (((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v3_pre_topc(B, A)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_tops_1)).
% 3.11/1.50  tff(c_56, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.11/1.50  tff(c_54, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.11/1.50  tff(c_52, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.11/1.50  tff(c_46, plain, (k1_xboole_0='#skF_5'), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.11/1.50  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.11/1.50  tff(c_75, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2])).
% 3.11/1.50  tff(c_28, plain, (![A_24]: (r2_hidden('#skF_1'(A_24), A_24) | k1_xboole_0=A_24)), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.11/1.50  tff(c_65, plain, (![A_24]: (r2_hidden('#skF_1'(A_24), A_24) | A_24='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_28])).
% 3.11/1.50  tff(c_34, plain, (![A_48]: (v4_pre_topc(k2_struct_0(A_48), A_48) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.11/1.50  tff(c_32, plain, (![A_47]: (l1_struct_0(A_47) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.11/1.50  tff(c_109, plain, (![A_71]: (u1_struct_0(A_71)=k2_struct_0(A_71) | ~l1_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.11/1.50  tff(c_120, plain, (![A_75]: (u1_struct_0(A_75)=k2_struct_0(A_75) | ~l1_pre_topc(A_75))), inference(resolution, [status(thm)], [c_32, c_109])).
% 3.11/1.50  tff(c_124, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_120])).
% 3.11/1.50  tff(c_50, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.11/1.50  tff(c_125, plain, (m1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_50])).
% 3.11/1.50  tff(c_16, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.11/1.50  tff(c_68, plain, (![A_8]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_16])).
% 3.11/1.50  tff(c_152, plain, (![C_80, B_81, A_82]: (~v1_xboole_0(C_80) | ~m1_subset_1(B_81, k1_zfmisc_1(C_80)) | ~r2_hidden(A_82, B_81))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.11/1.50  tff(c_158, plain, (![A_8, A_82]: (~v1_xboole_0(A_8) | ~r2_hidden(A_82, '#skF_5'))), inference(resolution, [status(thm)], [c_68, c_152])).
% 3.11/1.50  tff(c_170, plain, (![A_82]: (~r2_hidden(A_82, '#skF_5'))), inference(splitLeft, [status(thm)], [c_158])).
% 3.11/1.50  tff(c_6, plain, (![A_2]: (k1_subset_1(A_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.11/1.50  tff(c_72, plain, (![A_2]: (k1_subset_1(A_2)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_6])).
% 3.11/1.50  tff(c_8, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.11/1.50  tff(c_14, plain, (![A_7]: (k3_subset_1(A_7, k1_subset_1(A_7))=k2_subset_1(A_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.11/1.50  tff(c_70, plain, (![A_7]: (k3_subset_1(A_7, k1_subset_1(A_7))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14])).
% 3.11/1.50  tff(c_73, plain, (![A_7]: (k3_subset_1(A_7, '#skF_5')=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70])).
% 3.11/1.50  tff(c_18, plain, (![C_15, A_9, B_13]: (r2_hidden(C_15, k3_subset_1(A_9, B_13)) | r2_hidden(C_15, B_13) | ~m1_subset_1(C_15, A_9) | ~m1_subset_1(B_13, k1_zfmisc_1(A_9)) | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.11/1.50  tff(c_361, plain, (![C_106, A_107, B_108]: (r2_hidden(C_106, k3_subset_1(A_107, B_108)) | r2_hidden(C_106, B_108) | ~m1_subset_1(C_106, A_107) | ~m1_subset_1(B_108, k1_zfmisc_1(A_107)) | A_107='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_18])).
% 3.11/1.50  tff(c_376, plain, (![C_106, A_7]: (r2_hidden(C_106, A_7) | r2_hidden(C_106, '#skF_5') | ~m1_subset_1(C_106, A_7) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_7)) | A_7='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_73, c_361])).
% 3.11/1.50  tff(c_384, plain, (![C_106, A_7]: (r2_hidden(C_106, A_7) | r2_hidden(C_106, '#skF_5') | ~m1_subset_1(C_106, A_7) | A_7='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_376])).
% 3.11/1.50  tff(c_385, plain, (![C_106, A_7]: (r2_hidden(C_106, A_7) | ~m1_subset_1(C_106, A_7) | A_7='#skF_5')), inference(negUnitSimplification, [status(thm)], [c_170, c_384])).
% 3.11/1.50  tff(c_36, plain, (![A_49]: (v3_pre_topc(k2_struct_0(A_49), A_49) | ~l1_pre_topc(A_49) | ~v2_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.11/1.50  tff(c_10, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.11/1.50  tff(c_71, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 3.11/1.50  tff(c_58, plain, (![D_63]: (r2_hidden(D_63, '#skF_5') | ~r2_hidden('#skF_4', D_63) | ~v4_pre_topc(D_63, '#skF_3') | ~v3_pre_topc(D_63, '#skF_3') | ~m1_subset_1(D_63, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.11/1.50  tff(c_299, plain, (![D_63]: (r2_hidden(D_63, '#skF_5') | ~r2_hidden('#skF_4', D_63) | ~v4_pre_topc(D_63, '#skF_3') | ~v3_pre_topc(D_63, '#skF_3') | ~m1_subset_1(D_63, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_58])).
% 3.11/1.50  tff(c_301, plain, (![D_104]: (~r2_hidden('#skF_4', D_104) | ~v4_pre_topc(D_104, '#skF_3') | ~v3_pre_topc(D_104, '#skF_3') | ~m1_subset_1(D_104, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_170, c_299])).
% 3.11/1.50  tff(c_319, plain, (~r2_hidden('#skF_4', k2_struct_0('#skF_3')) | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_71, c_301])).
% 3.11/1.50  tff(c_445, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_319])).
% 3.11/1.50  tff(c_448, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_445])).
% 3.11/1.50  tff(c_452, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_448])).
% 3.11/1.50  tff(c_453, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~r2_hidden('#skF_4', k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_319])).
% 3.11/1.50  tff(c_466, plain, (~r2_hidden('#skF_4', k2_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_453])).
% 3.11/1.50  tff(c_469, plain, (~m1_subset_1('#skF_4', k2_struct_0('#skF_3')) | k2_struct_0('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_385, c_466])).
% 3.11/1.50  tff(c_472, plain, (k2_struct_0('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_125, c_469])).
% 3.11/1.50  tff(c_273, plain, (![A_103]: (m1_subset_1('#skF_2'(A_103), k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103) | ~v2_pre_topc(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.11/1.50  tff(c_282, plain, (m1_subset_1('#skF_2'('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_124, c_273])).
% 3.11/1.50  tff(c_287, plain, (m1_subset_1('#skF_2'('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_282])).
% 3.11/1.50  tff(c_288, plain, (m1_subset_1('#skF_2'('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_56, c_287])).
% 3.11/1.50  tff(c_22, plain, (![C_21, B_20, A_19]: (~v1_xboole_0(C_21) | ~m1_subset_1(B_20, k1_zfmisc_1(C_21)) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.11/1.50  tff(c_297, plain, (![A_19]: (~v1_xboole_0(k2_struct_0('#skF_3')) | ~r2_hidden(A_19, '#skF_2'('#skF_3')))), inference(resolution, [status(thm)], [c_288, c_22])).
% 3.11/1.50  tff(c_298, plain, (~v1_xboole_0(k2_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_297])).
% 3.11/1.50  tff(c_480, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_472, c_298])).
% 3.11/1.50  tff(c_486, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_480])).
% 3.11/1.50  tff(c_487, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_453])).
% 3.11/1.50  tff(c_492, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_487])).
% 3.11/1.50  tff(c_496, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_492])).
% 3.11/1.50  tff(c_550, plain, (![A_123]: (~r2_hidden(A_123, '#skF_2'('#skF_3')))), inference(splitRight, [status(thm)], [c_297])).
% 3.11/1.50  tff(c_555, plain, ('#skF_2'('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_65, c_550])).
% 3.11/1.50  tff(c_42, plain, (![A_50]: (~v1_xboole_0('#skF_2'(A_50)) | ~l1_pre_topc(A_50) | ~v2_pre_topc(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.11/1.50  tff(c_586, plain, (~v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_555, c_42])).
% 3.11/1.50  tff(c_599, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_75, c_586])).
% 3.11/1.50  tff(c_601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_599])).
% 3.11/1.50  tff(c_602, plain, (![A_8]: (~v1_xboole_0(A_8))), inference(splitRight, [status(thm)], [c_158])).
% 3.11/1.50  tff(c_604, plain, $false, inference(negUnitSimplification, [status(thm)], [c_602, c_75])).
% 3.11/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.50  
% 3.11/1.50  Inference rules
% 3.11/1.50  ----------------------
% 3.11/1.51  #Ref     : 0
% 3.11/1.51  #Sup     : 106
% 3.11/1.51  #Fact    : 0
% 3.11/1.51  #Define  : 0
% 3.11/1.51  #Split   : 7
% 3.11/1.51  #Chain   : 0
% 3.11/1.51  #Close   : 0
% 3.11/1.51  
% 3.11/1.51  Ordering : KBO
% 3.11/1.51  
% 3.11/1.51  Simplification rules
% 3.11/1.51  ----------------------
% 3.11/1.51  #Subsume      : 26
% 3.11/1.51  #Demod        : 83
% 3.11/1.51  #Tautology    : 40
% 3.11/1.51  #SimpNegUnit  : 16
% 3.11/1.51  #BackRed      : 21
% 3.11/1.51  
% 3.11/1.51  #Partial instantiations: 0
% 3.11/1.51  #Strategies tried      : 1
% 3.11/1.51  
% 3.11/1.51  Timing (in seconds)
% 3.11/1.51  ----------------------
% 3.11/1.51  Preprocessing        : 0.37
% 3.11/1.51  Parsing              : 0.20
% 3.11/1.51  CNF conversion       : 0.03
% 3.11/1.51  Main loop            : 0.35
% 3.11/1.51  Inferencing          : 0.12
% 3.11/1.51  Reduction            : 0.11
% 3.11/1.51  Demodulation         : 0.08
% 3.11/1.51  BG Simplification    : 0.02
% 3.11/1.51  Subsumption          : 0.06
% 3.11/1.51  Abstraction          : 0.02
% 3.11/1.51  MUC search           : 0.00
% 3.11/1.51  Cooper               : 0.00
% 3.11/1.51  Total                : 0.76
% 3.11/1.51  Index Insertion      : 0.00
% 3.11/1.51  Index Deletion       : 0.00
% 3.11/1.51  Index Matching       : 0.00
% 3.11/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
