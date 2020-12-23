%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:22 EST 2020

% Result     : Theorem 7.56s
% Output     : CNFRefutation 7.69s
% Verified   : 
% Statistics : Number of formulae       :  225 ( 885 expanded)
%              Number of leaves         :   30 ( 311 expanded)
%              Depth                    :   14
%              Number of atoms          :  507 (3569 expanded)
%              Number of equality atoms :   52 ( 179 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_tops_1 > v4_tops_1 > v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v4_tops_1,type,(
    v4_tops_1: ( $i * $i ) > $o )).

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff(v5_tops_1,type,(
    v5_tops_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_143,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( ( ( v4_pre_topc(D,B)
                          & v4_tops_1(D,B) )
                       => v5_tops_1(D,B) )
                      & ( v5_tops_1(C,A)
                       => ( v4_pre_topc(C,A)
                          & v4_tops_1(C,A) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tops_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_tops_1(B,A)
          <=> ( r1_tarski(k1_tops_1(A,k2_pre_topc(A,B)),B)
              & r1_tarski(B,k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v4_pre_topc(B,A)
                  & r1_tarski(C,B) )
               => r1_tarski(k2_pre_topc(A,C),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

tff(f_117,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,k1_tops_1(A,B)) = k2_pre_topc(A,k1_tops_1(A,k2_pre_topc(A,k1_tops_1(A,B)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_tops_1)).

tff(c_46,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_5718,plain,(
    ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_50,plain,
    ( ~ v5_tops_1('#skF_4','#skF_2')
    | v5_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_57,plain,(
    ~ v5_tops_1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_38,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_68,plain,(
    ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_54,plain,
    ( v4_pre_topc('#skF_4','#skF_2')
    | v5_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_58,plain,(
    v5_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_150,plain,(
    ! [A_63,B_64] :
      ( k2_pre_topc(A_63,k1_tops_1(A_63,B_64)) = B_64
      | ~ v5_tops_1(B_64,A_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_158,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v5_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_150])).

tff(c_166,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_58,c_158])).

tff(c_107,plain,(
    ! [A_57,B_58] :
      ( m1_subset_1(k1_tops_1(A_57,B_58),k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_28,plain,(
    ! [A_25,B_26] :
      ( v4_pre_topc(k2_pre_topc(A_25,B_26),A_25)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_325,plain,(
    ! [A_73,B_74] :
      ( v4_pre_topc(k2_pre_topc(A_73,k1_tops_1(A_73,B_74)),A_73)
      | ~ v2_pre_topc(A_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(resolution,[status(thm)],[c_107,c_28])).

tff(c_331,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_325])).

tff(c_333,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_42,c_331])).

tff(c_335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_333])).

tff(c_337,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_48,plain,
    ( v4_pre_topc('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_339,plain,
    ( v4_pre_topc('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_48])).

tff(c_340,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_339])).

tff(c_651,plain,(
    ! [A_109,B_110] :
      ( k2_pre_topc(A_109,k1_tops_1(A_109,B_110)) = B_110
      | ~ v5_tops_1(B_110,A_109)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_659,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v5_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_651])).

tff(c_667,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_58,c_659])).

tff(c_618,plain,(
    ! [A_105,B_106] :
      ( m1_subset_1(k1_tops_1(A_105,B_106),k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_12,plain,(
    ! [B_9,A_7] :
      ( r1_tarski(B_9,k2_pre_topc(A_7,B_9))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_737,plain,(
    ! [A_119,B_120] :
      ( r1_tarski(k1_tops_1(A_119,B_120),k2_pre_topc(A_119,k1_tops_1(A_119,B_120)))
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119) ) ),
    inference(resolution,[status(thm)],[c_618,c_12])).

tff(c_742,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_667,c_737])).

tff(c_745,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_742])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_422,plain,(
    ! [A_87,B_88] :
      ( k2_pre_topc(A_87,k1_tops_1(A_87,B_88)) = B_88
      | ~ v5_tops_1(B_88,A_87)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_430,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v5_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_422])).

tff(c_438,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_58,c_430])).

tff(c_26,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(k1_tops_1(A_23,B_24),k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_386,plain,(
    ! [A_83,B_84] :
      ( k2_pre_topc(A_83,k2_pre_topc(A_83,B_84)) = k2_pre_topc(A_83,B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_570,plain,(
    ! [A_101,B_102] :
      ( k2_pre_topc(A_101,k2_pre_topc(A_101,k1_tops_1(A_101,B_102))) = k2_pre_topc(A_101,k1_tops_1(A_101,B_102))
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101) ) ),
    inference(resolution,[status(thm)],[c_26,c_386])).

tff(c_578,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_570])).

tff(c_586,plain,(
    k2_pre_topc('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_438,c_438,c_578])).

tff(c_341,plain,(
    ! [B_75,A_76] :
      ( r1_tarski(B_75,k2_pre_topc(A_76,B_75))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_345,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_341])).

tff(c_351,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_345])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_357,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = '#skF_3'
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_351,c_2])).

tff(c_370,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_357])).

tff(c_588,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_370])).

tff(c_593,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_588])).

tff(c_594,plain,(
    k2_pre_topc('#skF_1','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_357])).

tff(c_1386,plain,(
    ! [B_146,A_147] :
      ( v4_tops_1(B_146,A_147)
      | ~ r1_tarski(B_146,k2_pre_topc(A_147,k1_tops_1(A_147,B_146)))
      | ~ r1_tarski(k1_tops_1(A_147,k2_pre_topc(A_147,B_146)),B_146)
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0(A_147)))
      | ~ l1_pre_topc(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1410,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_594,c_1386])).

tff(c_1427,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_745,c_6,c_667,c_1410])).

tff(c_1429,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_340,c_1427])).

tff(c_1431,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_339])).

tff(c_336,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | v4_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1433,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1431,c_336])).

tff(c_18,plain,(
    ! [B_19,A_17] :
      ( r1_tarski(B_19,k2_pre_topc(A_17,k1_tops_1(A_17,B_19)))
      | ~ v4_tops_1(B_19,A_17)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1434,plain,(
    ! [B_148,A_149] :
      ( r1_tarski(B_148,k2_pre_topc(A_149,B_148))
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ l1_pre_topc(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1436,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_1434])).

tff(c_1441,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1436])).

tff(c_1447,plain,
    ( k2_pre_topc('#skF_2','#skF_4') = '#skF_4'
    | ~ r1_tarski(k2_pre_topc('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1441,c_2])).

tff(c_1451,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_2','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1447])).

tff(c_1430,plain,(
    v4_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_339])).

tff(c_2196,plain,(
    ! [A_212,C_213,B_214] :
      ( r1_tarski(k2_pre_topc(A_212,C_213),B_214)
      | ~ r1_tarski(C_213,B_214)
      | ~ v4_pre_topc(B_214,A_212)
      | ~ m1_subset_1(C_213,k1_zfmisc_1(u1_struct_0(A_212)))
      | ~ m1_subset_1(B_214,k1_zfmisc_1(u1_struct_0(A_212)))
      | ~ l1_pre_topc(A_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2204,plain,(
    ! [B_214] :
      ( r1_tarski(k2_pre_topc('#skF_2','#skF_4'),B_214)
      | ~ r1_tarski('#skF_4',B_214)
      | ~ v4_pre_topc(B_214,'#skF_2')
      | ~ m1_subset_1(B_214,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_34,c_2196])).

tff(c_2239,plain,(
    ! [B_216] :
      ( r1_tarski(k2_pre_topc('#skF_2','#skF_4'),B_216)
      | ~ r1_tarski('#skF_4',B_216)
      | ~ v4_pre_topc(B_216,'#skF_2')
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2204])).

tff(c_2253,plain,
    ( r1_tarski(k2_pre_topc('#skF_2','#skF_4'),'#skF_4')
    | ~ r1_tarski('#skF_4','#skF_4')
    | ~ v4_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_2239])).

tff(c_2265,plain,(
    r1_tarski(k2_pre_topc('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1430,c_6,c_2253])).

tff(c_2267,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1451,c_2265])).

tff(c_2268,plain,(
    k2_pre_topc('#skF_2','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1447])).

tff(c_3170,plain,(
    ! [A_276,B_277] :
      ( r1_tarski(k1_tops_1(A_276,k2_pre_topc(A_276,B_277)),B_277)
      | ~ v4_tops_1(B_277,A_276)
      | ~ m1_subset_1(B_277,k1_zfmisc_1(u1_struct_0(A_276)))
      | ~ l1_pre_topc(A_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3181,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2268,c_3170])).

tff(c_3188,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_1433,c_3181])).

tff(c_3071,plain,(
    ! [A_266,B_267] :
      ( k2_pre_topc(A_266,k2_pre_topc(A_266,B_267)) = k2_pre_topc(A_266,B_267)
      | ~ m1_subset_1(B_267,k1_zfmisc_1(u1_struct_0(A_266)))
      | ~ l1_pre_topc(A_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3272,plain,(
    ! [A_286,B_287] :
      ( k2_pre_topc(A_286,k2_pre_topc(A_286,k1_tops_1(A_286,B_287))) = k2_pre_topc(A_286,k1_tops_1(A_286,B_287))
      | ~ m1_subset_1(B_287,k1_zfmisc_1(u1_struct_0(A_286)))
      | ~ l1_pre_topc(A_286) ) ),
    inference(resolution,[status(thm)],[c_26,c_3071])).

tff(c_3278,plain,
    ( k2_pre_topc('#skF_2',k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4'))) = k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_3272])).

tff(c_3285,plain,(
    k2_pre_topc('#skF_2',k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4'))) = k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_3278])).

tff(c_3047,plain,(
    ! [A_262,B_263] :
      ( m1_subset_1(k2_pre_topc(A_262,B_263),k1_zfmisc_1(u1_struct_0(A_262)))
      | ~ m1_subset_1(B_263,k1_zfmisc_1(u1_struct_0(A_262)))
      | ~ l1_pre_topc(A_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3058,plain,(
    ! [A_262,B_263] :
      ( v4_pre_topc(k2_pre_topc(A_262,k2_pre_topc(A_262,B_263)),A_262)
      | ~ v2_pre_topc(A_262)
      | ~ m1_subset_1(B_263,k1_zfmisc_1(u1_struct_0(A_262)))
      | ~ l1_pre_topc(A_262) ) ),
    inference(resolution,[status(thm)],[c_3047,c_28])).

tff(c_3307,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')),'#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3285,c_3058])).

tff(c_3324,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')),'#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_3307])).

tff(c_3328,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_3324])).

tff(c_3332,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_3328])).

tff(c_3336,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_3332])).

tff(c_3338,plain,(
    m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_3324])).

tff(c_3365,plain,(
    ! [A_288,B_289,C_290] :
      ( r1_tarski(k2_pre_topc(A_288,B_289),k2_pre_topc(A_288,C_290))
      | ~ r1_tarski(B_289,C_290)
      | ~ m1_subset_1(C_290,k1_zfmisc_1(u1_struct_0(A_288)))
      | ~ m1_subset_1(B_289,k1_zfmisc_1(u1_struct_0(A_288)))
      | ~ l1_pre_topc(A_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3397,plain,(
    ! [B_289] :
      ( r1_tarski(k2_pre_topc('#skF_2',B_289),'#skF_4')
      | ~ r1_tarski(B_289,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_289,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2268,c_3365])).

tff(c_3418,plain,(
    ! [B_291] :
      ( r1_tarski(k2_pre_topc('#skF_2',B_291),'#skF_4')
      | ~ r1_tarski(B_291,'#skF_4')
      | ~ m1_subset_1(B_291,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_3397])).

tff(c_3421,plain,
    ( r1_tarski(k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')),'#skF_4')
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_3338,c_3418])).

tff(c_3435,plain,(
    r1_tarski(k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3188,c_3421])).

tff(c_3447,plain,
    ( k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_3435,c_2])).

tff(c_3515,plain,(
    ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_3447])).

tff(c_3518,plain,
    ( ~ v4_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_3515])).

tff(c_3522,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_1433,c_3518])).

tff(c_3523,plain,(
    k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3447])).

tff(c_22,plain,(
    ! [B_22,A_20] :
      ( v5_tops_1(B_22,A_20)
      | k2_pre_topc(A_20,k1_tops_1(A_20,B_22)) != B_22
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3585,plain,
    ( v5_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3523,c_22])).

tff(c_3613,plain,(
    v5_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_3585])).

tff(c_3615,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_3613])).

tff(c_3617,plain,(
    ~ v5_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | v5_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_3618,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_3617,c_52])).

tff(c_3628,plain,(
    ! [B_300,A_301] :
      ( r1_tarski(B_300,k2_pre_topc(A_301,B_300))
      | ~ m1_subset_1(B_300,k1_zfmisc_1(u1_struct_0(A_301)))
      | ~ l1_pre_topc(A_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3630,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_3628])).

tff(c_3635,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_3630])).

tff(c_3652,plain,
    ( k2_pre_topc('#skF_2','#skF_4') = '#skF_4'
    | ~ r1_tarski(k2_pre_topc('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_3635,c_2])).

tff(c_3657,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_2','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3652])).

tff(c_3616,plain,(
    v4_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_4160,plain,(
    ! [A_333,C_334,B_335] :
      ( r1_tarski(k2_pre_topc(A_333,C_334),B_335)
      | ~ r1_tarski(C_334,B_335)
      | ~ v4_pre_topc(B_335,A_333)
      | ~ m1_subset_1(C_334,k1_zfmisc_1(u1_struct_0(A_333)))
      | ~ m1_subset_1(B_335,k1_zfmisc_1(u1_struct_0(A_333)))
      | ~ l1_pre_topc(A_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_4172,plain,(
    ! [B_335] :
      ( r1_tarski(k2_pre_topc('#skF_2','#skF_4'),B_335)
      | ~ r1_tarski('#skF_4',B_335)
      | ~ v4_pre_topc(B_335,'#skF_2')
      | ~ m1_subset_1(B_335,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_34,c_4160])).

tff(c_4192,plain,(
    ! [B_336] :
      ( r1_tarski(k2_pre_topc('#skF_2','#skF_4'),B_336)
      | ~ r1_tarski('#skF_4',B_336)
      | ~ v4_pre_topc(B_336,'#skF_2')
      | ~ m1_subset_1(B_336,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4172])).

tff(c_4206,plain,
    ( r1_tarski(k2_pre_topc('#skF_2','#skF_4'),'#skF_4')
    | ~ r1_tarski('#skF_4','#skF_4')
    | ~ v4_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_4192])).

tff(c_4218,plain,(
    r1_tarski(k2_pre_topc('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3616,c_6,c_4206])).

tff(c_4220,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3657,c_4218])).

tff(c_4221,plain,(
    k2_pre_topc('#skF_2','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3652])).

tff(c_4310,plain,(
    ! [A_349,B_350] :
      ( r1_tarski(k1_tops_1(A_349,k2_pre_topc(A_349,B_350)),B_350)
      | ~ v4_tops_1(B_350,A_349)
      | ~ m1_subset_1(B_350,k1_zfmisc_1(u1_struct_0(A_349)))
      | ~ l1_pre_topc(A_349) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4318,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4221,c_4310])).

tff(c_4323,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_3618,c_4318])).

tff(c_4584,plain,(
    ! [A_363,B_364,C_365] :
      ( r1_tarski(k2_pre_topc(A_363,B_364),k2_pre_topc(A_363,C_365))
      | ~ r1_tarski(B_364,C_365)
      | ~ m1_subset_1(C_365,k1_zfmisc_1(u1_struct_0(A_363)))
      | ~ m1_subset_1(B_364,k1_zfmisc_1(u1_struct_0(A_363)))
      | ~ l1_pre_topc(A_363) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4616,plain,(
    ! [B_364] :
      ( r1_tarski(k2_pre_topc('#skF_2',B_364),'#skF_4')
      | ~ r1_tarski(B_364,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_364,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4221,c_4584])).

tff(c_4655,plain,(
    ! [B_367] :
      ( r1_tarski(k2_pre_topc('#skF_2',B_367),'#skF_4')
      | ~ r1_tarski(B_367,'#skF_4')
      | ~ m1_subset_1(B_367,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_4616])).

tff(c_4663,plain,(
    ! [B_24] :
      ( r1_tarski(k2_pre_topc('#skF_2',k1_tops_1('#skF_2',B_24)),'#skF_4')
      | ~ r1_tarski(k1_tops_1('#skF_2',B_24),'#skF_4')
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_4655])).

tff(c_4672,plain,(
    ! [B_24] :
      ( r1_tarski(k2_pre_topc('#skF_2',k1_tops_1('#skF_2',B_24)),'#skF_4')
      | ~ r1_tarski(k1_tops_1('#skF_2',B_24),'#skF_4')
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4663])).

tff(c_4358,plain,(
    ! [B_355,A_356] :
      ( r1_tarski(B_355,k2_pre_topc(A_356,k1_tops_1(A_356,B_355)))
      | ~ v4_tops_1(B_355,A_356)
      | ~ m1_subset_1(B_355,k1_zfmisc_1(u1_struct_0(A_356)))
      | ~ l1_pre_topc(A_356) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_5598,plain,(
    ! [A_393,B_394] :
      ( k2_pre_topc(A_393,k1_tops_1(A_393,B_394)) = B_394
      | ~ r1_tarski(k2_pre_topc(A_393,k1_tops_1(A_393,B_394)),B_394)
      | ~ v4_tops_1(B_394,A_393)
      | ~ m1_subset_1(B_394,k1_zfmisc_1(u1_struct_0(A_393)))
      | ~ l1_pre_topc(A_393) ) ),
    inference(resolution,[status(thm)],[c_4358,c_2])).

tff(c_5606,plain,
    ( k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_4672,c_5598])).

tff(c_5623,plain,(
    k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4323,c_38,c_3618,c_5606])).

tff(c_4499,plain,(
    ! [A_361,B_362] :
      ( k2_pre_topc(A_361,k1_tops_1(A_361,k2_pre_topc(A_361,k1_tops_1(A_361,B_362)))) = k2_pre_topc(A_361,k1_tops_1(A_361,B_362))
      | ~ m1_subset_1(B_362,k1_zfmisc_1(u1_struct_0(A_361)))
      | ~ l1_pre_topc(A_361) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_4542,plain,(
    ! [A_361,B_362] :
      ( v5_tops_1(k2_pre_topc(A_361,k1_tops_1(A_361,B_362)),A_361)
      | ~ m1_subset_1(k2_pre_topc(A_361,k1_tops_1(A_361,B_362)),k1_zfmisc_1(u1_struct_0(A_361)))
      | ~ m1_subset_1(B_362,k1_zfmisc_1(u1_struct_0(A_361)))
      | ~ l1_pre_topc(A_361) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4499,c_22])).

tff(c_5644,plain,
    ( v5_tops_1(k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')),'#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5623,c_4542])).

tff(c_5704,plain,(
    v5_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_34,c_5623,c_5644])).

tff(c_5706,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_5704])).

tff(c_5707,plain,(
    v5_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_5801,plain,(
    ! [A_409,B_410] :
      ( k2_pre_topc(A_409,k1_tops_1(A_409,B_410)) = B_410
      | ~ v5_tops_1(B_410,A_409)
      | ~ m1_subset_1(B_410,k1_zfmisc_1(u1_struct_0(A_409)))
      | ~ l1_pre_topc(A_409) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_5809,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v5_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_5801])).

tff(c_5817,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5707,c_5809])).

tff(c_5758,plain,(
    ! [A_405,B_406] :
      ( m1_subset_1(k1_tops_1(A_405,B_406),k1_zfmisc_1(u1_struct_0(A_405)))
      | ~ m1_subset_1(B_406,k1_zfmisc_1(u1_struct_0(A_405)))
      | ~ l1_pre_topc(A_405) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_5878,plain,(
    ! [A_415,B_416] :
      ( v4_pre_topc(k2_pre_topc(A_415,k1_tops_1(A_415,B_416)),A_415)
      | ~ v2_pre_topc(A_415)
      | ~ m1_subset_1(B_416,k1_zfmisc_1(u1_struct_0(A_415)))
      | ~ l1_pre_topc(A_415) ) ),
    inference(resolution,[status(thm)],[c_5758,c_28])).

tff(c_5881,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5817,c_5878])).

tff(c_5886,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_42,c_5881])).

tff(c_5888,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5718,c_5886])).

tff(c_5890,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_5892,plain,
    ( v4_pre_topc('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5890,c_48])).

tff(c_5893,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_5892])).

tff(c_8405,plain,(
    ! [A_552,B_553] :
      ( k2_pre_topc(A_552,k1_tops_1(A_552,B_553)) = B_553
      | ~ v5_tops_1(B_553,A_552)
      | ~ m1_subset_1(B_553,k1_zfmisc_1(u1_struct_0(A_552)))
      | ~ l1_pre_topc(A_552) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_8413,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v5_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_8405])).

tff(c_8421,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5707,c_8413])).

tff(c_5910,plain,(
    ! [A_419,B_420] :
      ( m1_subset_1(k1_tops_1(A_419,B_420),k1_zfmisc_1(u1_struct_0(A_419)))
      | ~ m1_subset_1(B_420,k1_zfmisc_1(u1_struct_0(A_419)))
      | ~ l1_pre_topc(A_419) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_8451,plain,(
    ! [A_556,B_557] :
      ( r1_tarski(k1_tops_1(A_556,B_557),k2_pre_topc(A_556,k1_tops_1(A_556,B_557)))
      | ~ m1_subset_1(B_557,k1_zfmisc_1(u1_struct_0(A_556)))
      | ~ l1_pre_topc(A_556) ) ),
    inference(resolution,[status(thm)],[c_5910,c_12])).

tff(c_8456,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8421,c_8451])).

tff(c_8462,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_8456])).

tff(c_7737,plain,(
    ! [A_516,B_517] :
      ( k2_pre_topc(A_516,k1_tops_1(A_516,B_517)) = B_517
      | ~ v5_tops_1(B_517,A_516)
      | ~ m1_subset_1(B_517,k1_zfmisc_1(u1_struct_0(A_516)))
      | ~ l1_pre_topc(A_516) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_7745,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v5_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_7737])).

tff(c_7753,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5707,c_7745])).

tff(c_5896,plain,(
    ! [B_417,A_418] :
      ( r1_tarski(B_417,k2_pre_topc(A_418,B_417))
      | ~ m1_subset_1(B_417,k1_zfmisc_1(u1_struct_0(A_418)))
      | ~ l1_pre_topc(A_418) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_5900,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_5896])).

tff(c_5906,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5900])).

tff(c_5916,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = '#skF_3'
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_5906,c_2])).

tff(c_7692,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_5916])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k2_pre_topc(A_3,B_4),k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_7711,plain,(
    ! [A_514,B_515] :
      ( k2_pre_topc(A_514,k2_pre_topc(A_514,B_515)) = k2_pre_topc(A_514,B_515)
      | ~ m1_subset_1(B_515,k1_zfmisc_1(u1_struct_0(A_514)))
      | ~ l1_pre_topc(A_514) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_7719,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = k2_pre_topc('#skF_1','#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_7711])).

tff(c_7727,plain,(
    k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = k2_pre_topc('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_7719])).

tff(c_7809,plain,(
    ! [A_522,B_523] :
      ( r1_tarski(k1_tops_1(A_522,k2_pre_topc(A_522,B_523)),B_523)
      | ~ v4_tops_1(B_523,A_522)
      | ~ m1_subset_1(B_523,k1_zfmisc_1(u1_struct_0(A_522)))
      | ~ l1_pre_topc(A_522) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_7820,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')),k2_pre_topc('#skF_1','#skF_3'))
    | ~ v4_tops_1(k2_pre_topc('#skF_1','#skF_3'),'#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_7727,c_7809])).

tff(c_7830,plain,
    ( r1_tarski(k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')),k2_pre_topc('#skF_1','#skF_3'))
    | ~ v4_tops_1(k2_pre_topc('#skF_1','#skF_3'),'#skF_1')
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_7820])).

tff(c_7929,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_7830])).

tff(c_7932,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_7929])).

tff(c_7936,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_7932])).

tff(c_7938,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_7830])).

tff(c_8074,plain,(
    ! [A_538,B_539,C_540] :
      ( r1_tarski(k2_pre_topc(A_538,B_539),k2_pre_topc(A_538,C_540))
      | ~ r1_tarski(B_539,C_540)
      | ~ m1_subset_1(C_540,k1_zfmisc_1(u1_struct_0(A_538)))
      | ~ m1_subset_1(B_539,k1_zfmisc_1(u1_struct_0(A_538)))
      | ~ l1_pre_topc(A_538) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8097,plain,(
    ! [C_540] :
      ( r1_tarski(k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1',C_540))
      | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),C_540)
      | ~ m1_subset_1(C_540,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7727,c_8074])).

tff(c_8257,plain,(
    ! [C_544] :
      ( r1_tarski(k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1',C_544))
      | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),C_544)
      | ~ m1_subset_1(C_544,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_7938,c_8097])).

tff(c_8269,plain,
    ( r1_tarski(k2_pre_topc('#skF_1','#skF_3'),'#skF_3')
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),k1_tops_1('#skF_1','#skF_3'))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_7753,c_8257])).

tff(c_8277,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),k1_tops_1('#skF_1','#skF_3'))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_7692,c_8269])).

tff(c_8280,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_8277])).

tff(c_8283,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_8280])).

tff(c_8287,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_8283])).

tff(c_8289,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_8277])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k2_pre_topc(A_5,k2_pre_topc(A_5,B_6)) = k2_pre_topc(A_5,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8293,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8289,c_10])).

tff(c_8303,plain,(
    k2_pre_topc('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_7753,c_7753,c_8293])).

tff(c_8346,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8303,c_7692])).

tff(c_8355,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8346])).

tff(c_8356,plain,(
    k2_pre_topc('#skF_1','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5916])).

tff(c_8926,plain,(
    ! [B_586,A_587] :
      ( v4_tops_1(B_586,A_587)
      | ~ r1_tarski(B_586,k2_pre_topc(A_587,k1_tops_1(A_587,B_586)))
      | ~ r1_tarski(k1_tops_1(A_587,k2_pre_topc(A_587,B_586)),B_586)
      | ~ m1_subset_1(B_586,k1_zfmisc_1(u1_struct_0(A_587)))
      | ~ l1_pre_topc(A_587) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8941,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8356,c_8926])).

tff(c_8953,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_8462,c_6,c_8421,c_8941])).

tff(c_8955,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5893,c_8953])).

tff(c_8957,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_5892])).

tff(c_5708,plain,(
    v5_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_44,plain,
    ( ~ v5_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_8961,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5890,c_8957,c_5708,c_44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:53:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.56/2.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.56/2.53  
% 7.56/2.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.56/2.53  %$ v5_tops_1 > v4_tops_1 > v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.56/2.53  
% 7.56/2.53  %Foreground sorts:
% 7.56/2.53  
% 7.56/2.53  
% 7.56/2.53  %Background operators:
% 7.56/2.53  
% 7.56/2.53  
% 7.56/2.53  %Foreground operators:
% 7.56/2.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.56/2.53  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.56/2.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.56/2.53  tff(v4_tops_1, type, v4_tops_1: ($i * $i) > $o).
% 7.56/2.53  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 7.56/2.53  tff('#skF_2', type, '#skF_2': $i).
% 7.56/2.53  tff('#skF_3', type, '#skF_3': $i).
% 7.56/2.53  tff('#skF_1', type, '#skF_1': $i).
% 7.56/2.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.56/2.53  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 7.56/2.53  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 7.56/2.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.56/2.53  tff('#skF_4', type, '#skF_4': $i).
% 7.56/2.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.56/2.53  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.56/2.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.56/2.53  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 7.56/2.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.56/2.53  
% 7.69/2.56  tff(f_143, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (((v4_pre_topc(D, B) & v4_tops_1(D, B)) => v5_tops_1(D, B)) & (v5_tops_1(C, A) => (v4_pre_topc(C, A) & v4_tops_1(C, A)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_tops_1)).
% 7.69/2.56  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tops_1)).
% 7.69/2.56  tff(f_88, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 7.69/2.56  tff(f_96, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 7.69/2.56  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 7.69/2.56  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.69/2.56  tff(f_43, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k2_pre_topc(A, k2_pre_topc(A, B)) = k2_pre_topc(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', projectivity_k2_pre_topc)).
% 7.69/2.56  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_tops_1(B, A) <=> (r1_tarski(k1_tops_1(A, k2_pre_topc(A, B)), B) & r1_tarski(B, k2_pre_topc(A, k1_tops_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tops_1)).
% 7.69/2.56  tff(f_110, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & r1_tarski(C, B)) => r1_tarski(k2_pre_topc(A, C), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_1)).
% 7.69/2.56  tff(f_37, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 7.69/2.56  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_pre_topc)).
% 7.69/2.56  tff(f_117, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, k1_tops_1(A, B)) = k2_pre_topc(A, k1_tops_1(A, k2_pre_topc(A, k1_tops_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_tops_1)).
% 7.69/2.56  tff(c_46, plain, (v4_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.69/2.56  tff(c_5718, plain, (~v4_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 7.69/2.56  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.69/2.56  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.69/2.56  tff(c_42, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.69/2.56  tff(c_50, plain, (~v5_tops_1('#skF_4', '#skF_2') | v5_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.69/2.56  tff(c_57, plain, (~v5_tops_1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_50])).
% 7.69/2.56  tff(c_38, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.69/2.56  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.69/2.56  tff(c_68, plain, (~v4_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_46])).
% 7.69/2.56  tff(c_54, plain, (v4_pre_topc('#skF_4', '#skF_2') | v5_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.69/2.56  tff(c_58, plain, (v5_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_54])).
% 7.69/2.56  tff(c_150, plain, (![A_63, B_64]: (k2_pre_topc(A_63, k1_tops_1(A_63, B_64))=B_64 | ~v5_tops_1(B_64, A_63) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.69/2.56  tff(c_158, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3' | ~v5_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_150])).
% 7.69/2.56  tff(c_166, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_58, c_158])).
% 7.69/2.56  tff(c_107, plain, (![A_57, B_58]: (m1_subset_1(k1_tops_1(A_57, B_58), k1_zfmisc_1(u1_struct_0(A_57))) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.69/2.56  tff(c_28, plain, (![A_25, B_26]: (v4_pre_topc(k2_pre_topc(A_25, B_26), A_25) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.69/2.56  tff(c_325, plain, (![A_73, B_74]: (v4_pre_topc(k2_pre_topc(A_73, k1_tops_1(A_73, B_74)), A_73) | ~v2_pre_topc(A_73) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73))), inference(resolution, [status(thm)], [c_107, c_28])).
% 7.69/2.56  tff(c_331, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_166, c_325])).
% 7.69/2.56  tff(c_333, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_42, c_331])).
% 7.69/2.56  tff(c_335, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_333])).
% 7.69/2.56  tff(c_337, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 7.69/2.56  tff(c_48, plain, (v4_pre_topc('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.69/2.56  tff(c_339, plain, (v4_pre_topc('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_337, c_48])).
% 7.69/2.56  tff(c_340, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_339])).
% 7.69/2.56  tff(c_651, plain, (![A_109, B_110]: (k2_pre_topc(A_109, k1_tops_1(A_109, B_110))=B_110 | ~v5_tops_1(B_110, A_109) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.69/2.56  tff(c_659, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3' | ~v5_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_651])).
% 7.69/2.56  tff(c_667, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_58, c_659])).
% 7.69/2.56  tff(c_618, plain, (![A_105, B_106]: (m1_subset_1(k1_tops_1(A_105, B_106), k1_zfmisc_1(u1_struct_0(A_105))) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.69/2.56  tff(c_12, plain, (![B_9, A_7]: (r1_tarski(B_9, k2_pre_topc(A_7, B_9)) | ~m1_subset_1(B_9, k1_zfmisc_1(u1_struct_0(A_7))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.69/2.56  tff(c_737, plain, (![A_119, B_120]: (r1_tarski(k1_tops_1(A_119, B_120), k2_pre_topc(A_119, k1_tops_1(A_119, B_120))) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_pre_topc(A_119))), inference(resolution, [status(thm)], [c_618, c_12])).
% 7.69/2.56  tff(c_742, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_667, c_737])).
% 7.69/2.56  tff(c_745, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_742])).
% 7.69/2.56  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.69/2.56  tff(c_422, plain, (![A_87, B_88]: (k2_pre_topc(A_87, k1_tops_1(A_87, B_88))=B_88 | ~v5_tops_1(B_88, A_87) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.69/2.56  tff(c_430, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3' | ~v5_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_422])).
% 7.69/2.56  tff(c_438, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_58, c_430])).
% 7.69/2.56  tff(c_26, plain, (![A_23, B_24]: (m1_subset_1(k1_tops_1(A_23, B_24), k1_zfmisc_1(u1_struct_0(A_23))) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.69/2.56  tff(c_386, plain, (![A_83, B_84]: (k2_pre_topc(A_83, k2_pre_topc(A_83, B_84))=k2_pre_topc(A_83, B_84) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.69/2.56  tff(c_570, plain, (![A_101, B_102]: (k2_pre_topc(A_101, k2_pre_topc(A_101, k1_tops_1(A_101, B_102)))=k2_pre_topc(A_101, k1_tops_1(A_101, B_102)) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101))), inference(resolution, [status(thm)], [c_26, c_386])).
% 7.69/2.56  tff(c_578, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_570])).
% 7.69/2.56  tff(c_586, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_438, c_438, c_578])).
% 7.69/2.56  tff(c_341, plain, (![B_75, A_76]: (r1_tarski(B_75, k2_pre_topc(A_76, B_75)) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.69/2.56  tff(c_345, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_341])).
% 7.69/2.56  tff(c_351, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_345])).
% 7.69/2.56  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.69/2.56  tff(c_357, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3' | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_351, c_2])).
% 7.69/2.56  tff(c_370, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_357])).
% 7.69/2.56  tff(c_588, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_586, c_370])).
% 7.69/2.56  tff(c_593, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_588])).
% 7.69/2.56  tff(c_594, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_357])).
% 7.69/2.56  tff(c_1386, plain, (![B_146, A_147]: (v4_tops_1(B_146, A_147) | ~r1_tarski(B_146, k2_pre_topc(A_147, k1_tops_1(A_147, B_146))) | ~r1_tarski(k1_tops_1(A_147, k2_pre_topc(A_147, B_146)), B_146) | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0(A_147))) | ~l1_pre_topc(A_147))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.69/2.56  tff(c_1410, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_594, c_1386])).
% 7.69/2.56  tff(c_1427, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_745, c_6, c_667, c_1410])).
% 7.69/2.56  tff(c_1429, plain, $false, inference(negUnitSimplification, [status(thm)], [c_340, c_1427])).
% 7.69/2.56  tff(c_1431, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_339])).
% 7.69/2.56  tff(c_336, plain, (~v4_tops_1('#skF_3', '#skF_1') | v4_tops_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 7.69/2.56  tff(c_1433, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1431, c_336])).
% 7.69/2.56  tff(c_18, plain, (![B_19, A_17]: (r1_tarski(B_19, k2_pre_topc(A_17, k1_tops_1(A_17, B_19))) | ~v4_tops_1(B_19, A_17) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.69/2.56  tff(c_1434, plain, (![B_148, A_149]: (r1_tarski(B_148, k2_pre_topc(A_149, B_148)) | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0(A_149))) | ~l1_pre_topc(A_149))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.69/2.56  tff(c_1436, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_1434])).
% 7.69/2.56  tff(c_1441, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1436])).
% 7.69/2.56  tff(c_1447, plain, (k2_pre_topc('#skF_2', '#skF_4')='#skF_4' | ~r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_1441, c_2])).
% 7.69/2.56  tff(c_1451, plain, (~r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_1447])).
% 7.69/2.56  tff(c_1430, plain, (v4_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_339])).
% 7.69/2.56  tff(c_2196, plain, (![A_212, C_213, B_214]: (r1_tarski(k2_pre_topc(A_212, C_213), B_214) | ~r1_tarski(C_213, B_214) | ~v4_pre_topc(B_214, A_212) | ~m1_subset_1(C_213, k1_zfmisc_1(u1_struct_0(A_212))) | ~m1_subset_1(B_214, k1_zfmisc_1(u1_struct_0(A_212))) | ~l1_pre_topc(A_212))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.69/2.56  tff(c_2204, plain, (![B_214]: (r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), B_214) | ~r1_tarski('#skF_4', B_214) | ~v4_pre_topc(B_214, '#skF_2') | ~m1_subset_1(B_214, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_2196])).
% 7.69/2.56  tff(c_2239, plain, (![B_216]: (r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), B_216) | ~r1_tarski('#skF_4', B_216) | ~v4_pre_topc(B_216, '#skF_2') | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2204])).
% 7.69/2.56  tff(c_2253, plain, (r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), '#skF_4') | ~r1_tarski('#skF_4', '#skF_4') | ~v4_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_2239])).
% 7.69/2.56  tff(c_2265, plain, (r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1430, c_6, c_2253])).
% 7.69/2.56  tff(c_2267, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1451, c_2265])).
% 7.69/2.56  tff(c_2268, plain, (k2_pre_topc('#skF_2', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_1447])).
% 7.69/2.56  tff(c_3170, plain, (![A_276, B_277]: (r1_tarski(k1_tops_1(A_276, k2_pre_topc(A_276, B_277)), B_277) | ~v4_tops_1(B_277, A_276) | ~m1_subset_1(B_277, k1_zfmisc_1(u1_struct_0(A_276))) | ~l1_pre_topc(A_276))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.69/2.56  tff(c_3181, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v4_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2268, c_3170])).
% 7.69/2.56  tff(c_3188, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_1433, c_3181])).
% 7.69/2.56  tff(c_3071, plain, (![A_266, B_267]: (k2_pre_topc(A_266, k2_pre_topc(A_266, B_267))=k2_pre_topc(A_266, B_267) | ~m1_subset_1(B_267, k1_zfmisc_1(u1_struct_0(A_266))) | ~l1_pre_topc(A_266))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.69/2.56  tff(c_3272, plain, (![A_286, B_287]: (k2_pre_topc(A_286, k2_pre_topc(A_286, k1_tops_1(A_286, B_287)))=k2_pre_topc(A_286, k1_tops_1(A_286, B_287)) | ~m1_subset_1(B_287, k1_zfmisc_1(u1_struct_0(A_286))) | ~l1_pre_topc(A_286))), inference(resolution, [status(thm)], [c_26, c_3071])).
% 7.69/2.56  tff(c_3278, plain, (k2_pre_topc('#skF_2', k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4')))=k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_3272])).
% 7.69/2.56  tff(c_3285, plain, (k2_pre_topc('#skF_2', k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4')))=k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_3278])).
% 7.69/2.56  tff(c_3047, plain, (![A_262, B_263]: (m1_subset_1(k2_pre_topc(A_262, B_263), k1_zfmisc_1(u1_struct_0(A_262))) | ~m1_subset_1(B_263, k1_zfmisc_1(u1_struct_0(A_262))) | ~l1_pre_topc(A_262))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.69/2.56  tff(c_3058, plain, (![A_262, B_263]: (v4_pre_topc(k2_pre_topc(A_262, k2_pre_topc(A_262, B_263)), A_262) | ~v2_pre_topc(A_262) | ~m1_subset_1(B_263, k1_zfmisc_1(u1_struct_0(A_262))) | ~l1_pre_topc(A_262))), inference(resolution, [status(thm)], [c_3047, c_28])).
% 7.69/2.56  tff(c_3307, plain, (v4_pre_topc(k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4')), '#skF_2') | ~v2_pre_topc('#skF_2') | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3285, c_3058])).
% 7.69/2.56  tff(c_3324, plain, (v4_pre_topc(k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4')), '#skF_2') | ~v2_pre_topc('#skF_2') | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_3307])).
% 7.69/2.56  tff(c_3328, plain, (~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_3324])).
% 7.69/2.56  tff(c_3332, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_3328])).
% 7.69/2.56  tff(c_3336, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_3332])).
% 7.69/2.56  tff(c_3338, plain, (m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_3324])).
% 7.69/2.56  tff(c_3365, plain, (![A_288, B_289, C_290]: (r1_tarski(k2_pre_topc(A_288, B_289), k2_pre_topc(A_288, C_290)) | ~r1_tarski(B_289, C_290) | ~m1_subset_1(C_290, k1_zfmisc_1(u1_struct_0(A_288))) | ~m1_subset_1(B_289, k1_zfmisc_1(u1_struct_0(A_288))) | ~l1_pre_topc(A_288))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.69/2.56  tff(c_3397, plain, (![B_289]: (r1_tarski(k2_pre_topc('#skF_2', B_289), '#skF_4') | ~r1_tarski(B_289, '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_289, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2268, c_3365])).
% 7.69/2.56  tff(c_3418, plain, (![B_291]: (r1_tarski(k2_pre_topc('#skF_2', B_291), '#skF_4') | ~r1_tarski(B_291, '#skF_4') | ~m1_subset_1(B_291, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_3397])).
% 7.69/2.56  tff(c_3421, plain, (r1_tarski(k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4')), '#skF_4') | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_3338, c_3418])).
% 7.69/2.56  tff(c_3435, plain, (r1_tarski(k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3188, c_3421])).
% 7.69/2.56  tff(c_3447, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))='#skF_4' | ~r1_tarski('#skF_4', k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_3435, c_2])).
% 7.69/2.56  tff(c_3515, plain, (~r1_tarski('#skF_4', k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4')))), inference(splitLeft, [status(thm)], [c_3447])).
% 7.69/2.56  tff(c_3518, plain, (~v4_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_18, c_3515])).
% 7.69/2.56  tff(c_3522, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_1433, c_3518])).
% 7.69/2.56  tff(c_3523, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_3447])).
% 7.69/2.56  tff(c_22, plain, (![B_22, A_20]: (v5_tops_1(B_22, A_20) | k2_pre_topc(A_20, k1_tops_1(A_20, B_22))!=B_22 | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.69/2.56  tff(c_3585, plain, (v5_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3523, c_22])).
% 7.69/2.56  tff(c_3613, plain, (v5_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_3585])).
% 7.69/2.56  tff(c_3615, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_3613])).
% 7.69/2.56  tff(c_3617, plain, (~v5_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_54])).
% 7.69/2.56  tff(c_52, plain, (v4_tops_1('#skF_4', '#skF_2') | v5_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.69/2.56  tff(c_3618, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_3617, c_52])).
% 7.69/2.56  tff(c_3628, plain, (![B_300, A_301]: (r1_tarski(B_300, k2_pre_topc(A_301, B_300)) | ~m1_subset_1(B_300, k1_zfmisc_1(u1_struct_0(A_301))) | ~l1_pre_topc(A_301))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.69/2.56  tff(c_3630, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_3628])).
% 7.69/2.56  tff(c_3635, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_3630])).
% 7.69/2.56  tff(c_3652, plain, (k2_pre_topc('#skF_2', '#skF_4')='#skF_4' | ~r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_3635, c_2])).
% 7.69/2.56  tff(c_3657, plain, (~r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_3652])).
% 7.69/2.56  tff(c_3616, plain, (v4_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_54])).
% 7.69/2.56  tff(c_4160, plain, (![A_333, C_334, B_335]: (r1_tarski(k2_pre_topc(A_333, C_334), B_335) | ~r1_tarski(C_334, B_335) | ~v4_pre_topc(B_335, A_333) | ~m1_subset_1(C_334, k1_zfmisc_1(u1_struct_0(A_333))) | ~m1_subset_1(B_335, k1_zfmisc_1(u1_struct_0(A_333))) | ~l1_pre_topc(A_333))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.69/2.56  tff(c_4172, plain, (![B_335]: (r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), B_335) | ~r1_tarski('#skF_4', B_335) | ~v4_pre_topc(B_335, '#skF_2') | ~m1_subset_1(B_335, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_4160])).
% 7.69/2.56  tff(c_4192, plain, (![B_336]: (r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), B_336) | ~r1_tarski('#skF_4', B_336) | ~v4_pre_topc(B_336, '#skF_2') | ~m1_subset_1(B_336, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4172])).
% 7.69/2.56  tff(c_4206, plain, (r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), '#skF_4') | ~r1_tarski('#skF_4', '#skF_4') | ~v4_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_4192])).
% 7.69/2.56  tff(c_4218, plain, (r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3616, c_6, c_4206])).
% 7.69/2.56  tff(c_4220, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3657, c_4218])).
% 7.69/2.56  tff(c_4221, plain, (k2_pre_topc('#skF_2', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_3652])).
% 7.69/2.56  tff(c_4310, plain, (![A_349, B_350]: (r1_tarski(k1_tops_1(A_349, k2_pre_topc(A_349, B_350)), B_350) | ~v4_tops_1(B_350, A_349) | ~m1_subset_1(B_350, k1_zfmisc_1(u1_struct_0(A_349))) | ~l1_pre_topc(A_349))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.69/2.56  tff(c_4318, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v4_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4221, c_4310])).
% 7.69/2.56  tff(c_4323, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_3618, c_4318])).
% 7.69/2.56  tff(c_4584, plain, (![A_363, B_364, C_365]: (r1_tarski(k2_pre_topc(A_363, B_364), k2_pre_topc(A_363, C_365)) | ~r1_tarski(B_364, C_365) | ~m1_subset_1(C_365, k1_zfmisc_1(u1_struct_0(A_363))) | ~m1_subset_1(B_364, k1_zfmisc_1(u1_struct_0(A_363))) | ~l1_pre_topc(A_363))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.69/2.56  tff(c_4616, plain, (![B_364]: (r1_tarski(k2_pre_topc('#skF_2', B_364), '#skF_4') | ~r1_tarski(B_364, '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_364, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4221, c_4584])).
% 7.69/2.56  tff(c_4655, plain, (![B_367]: (r1_tarski(k2_pre_topc('#skF_2', B_367), '#skF_4') | ~r1_tarski(B_367, '#skF_4') | ~m1_subset_1(B_367, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_4616])).
% 7.69/2.56  tff(c_4663, plain, (![B_24]: (r1_tarski(k2_pre_topc('#skF_2', k1_tops_1('#skF_2', B_24)), '#skF_4') | ~r1_tarski(k1_tops_1('#skF_2', B_24), '#skF_4') | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_26, c_4655])).
% 7.69/2.56  tff(c_4672, plain, (![B_24]: (r1_tarski(k2_pre_topc('#skF_2', k1_tops_1('#skF_2', B_24)), '#skF_4') | ~r1_tarski(k1_tops_1('#skF_2', B_24), '#skF_4') | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4663])).
% 7.69/2.56  tff(c_4358, plain, (![B_355, A_356]: (r1_tarski(B_355, k2_pre_topc(A_356, k1_tops_1(A_356, B_355))) | ~v4_tops_1(B_355, A_356) | ~m1_subset_1(B_355, k1_zfmisc_1(u1_struct_0(A_356))) | ~l1_pre_topc(A_356))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.69/2.56  tff(c_5598, plain, (![A_393, B_394]: (k2_pre_topc(A_393, k1_tops_1(A_393, B_394))=B_394 | ~r1_tarski(k2_pre_topc(A_393, k1_tops_1(A_393, B_394)), B_394) | ~v4_tops_1(B_394, A_393) | ~m1_subset_1(B_394, k1_zfmisc_1(u1_struct_0(A_393))) | ~l1_pre_topc(A_393))), inference(resolution, [status(thm)], [c_4358, c_2])).
% 7.69/2.56  tff(c_5606, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))='#skF_4' | ~v4_tops_1('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_4672, c_5598])).
% 7.69/2.56  tff(c_5623, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_4323, c_38, c_3618, c_5606])).
% 7.69/2.56  tff(c_4499, plain, (![A_361, B_362]: (k2_pre_topc(A_361, k1_tops_1(A_361, k2_pre_topc(A_361, k1_tops_1(A_361, B_362))))=k2_pre_topc(A_361, k1_tops_1(A_361, B_362)) | ~m1_subset_1(B_362, k1_zfmisc_1(u1_struct_0(A_361))) | ~l1_pre_topc(A_361))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.69/2.56  tff(c_4542, plain, (![A_361, B_362]: (v5_tops_1(k2_pre_topc(A_361, k1_tops_1(A_361, B_362)), A_361) | ~m1_subset_1(k2_pre_topc(A_361, k1_tops_1(A_361, B_362)), k1_zfmisc_1(u1_struct_0(A_361))) | ~m1_subset_1(B_362, k1_zfmisc_1(u1_struct_0(A_361))) | ~l1_pre_topc(A_361))), inference(superposition, [status(thm), theory('equality')], [c_4499, c_22])).
% 7.69/2.56  tff(c_5644, plain, (v5_tops_1(k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4')), '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5623, c_4542])).
% 7.69/2.56  tff(c_5704, plain, (v5_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_34, c_5623, c_5644])).
% 7.69/2.56  tff(c_5706, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_5704])).
% 7.69/2.56  tff(c_5707, plain, (v5_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_50])).
% 7.69/2.56  tff(c_5801, plain, (![A_409, B_410]: (k2_pre_topc(A_409, k1_tops_1(A_409, B_410))=B_410 | ~v5_tops_1(B_410, A_409) | ~m1_subset_1(B_410, k1_zfmisc_1(u1_struct_0(A_409))) | ~l1_pre_topc(A_409))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.69/2.56  tff(c_5809, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3' | ~v5_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_5801])).
% 7.69/2.56  tff(c_5817, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_5707, c_5809])).
% 7.69/2.56  tff(c_5758, plain, (![A_405, B_406]: (m1_subset_1(k1_tops_1(A_405, B_406), k1_zfmisc_1(u1_struct_0(A_405))) | ~m1_subset_1(B_406, k1_zfmisc_1(u1_struct_0(A_405))) | ~l1_pre_topc(A_405))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.69/2.56  tff(c_5878, plain, (![A_415, B_416]: (v4_pre_topc(k2_pre_topc(A_415, k1_tops_1(A_415, B_416)), A_415) | ~v2_pre_topc(A_415) | ~m1_subset_1(B_416, k1_zfmisc_1(u1_struct_0(A_415))) | ~l1_pre_topc(A_415))), inference(resolution, [status(thm)], [c_5758, c_28])).
% 7.69/2.56  tff(c_5881, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5817, c_5878])).
% 7.69/2.56  tff(c_5886, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_42, c_5881])).
% 7.69/2.56  tff(c_5888, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5718, c_5886])).
% 7.69/2.56  tff(c_5890, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 7.69/2.56  tff(c_5892, plain, (v4_pre_topc('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5890, c_48])).
% 7.69/2.56  tff(c_5893, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_5892])).
% 7.69/2.56  tff(c_8405, plain, (![A_552, B_553]: (k2_pre_topc(A_552, k1_tops_1(A_552, B_553))=B_553 | ~v5_tops_1(B_553, A_552) | ~m1_subset_1(B_553, k1_zfmisc_1(u1_struct_0(A_552))) | ~l1_pre_topc(A_552))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.69/2.56  tff(c_8413, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3' | ~v5_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_8405])).
% 7.69/2.56  tff(c_8421, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_5707, c_8413])).
% 7.69/2.56  tff(c_5910, plain, (![A_419, B_420]: (m1_subset_1(k1_tops_1(A_419, B_420), k1_zfmisc_1(u1_struct_0(A_419))) | ~m1_subset_1(B_420, k1_zfmisc_1(u1_struct_0(A_419))) | ~l1_pre_topc(A_419))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.69/2.56  tff(c_8451, plain, (![A_556, B_557]: (r1_tarski(k1_tops_1(A_556, B_557), k2_pre_topc(A_556, k1_tops_1(A_556, B_557))) | ~m1_subset_1(B_557, k1_zfmisc_1(u1_struct_0(A_556))) | ~l1_pre_topc(A_556))), inference(resolution, [status(thm)], [c_5910, c_12])).
% 7.69/2.56  tff(c_8456, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8421, c_8451])).
% 7.69/2.56  tff(c_8462, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_8456])).
% 7.69/2.56  tff(c_7737, plain, (![A_516, B_517]: (k2_pre_topc(A_516, k1_tops_1(A_516, B_517))=B_517 | ~v5_tops_1(B_517, A_516) | ~m1_subset_1(B_517, k1_zfmisc_1(u1_struct_0(A_516))) | ~l1_pre_topc(A_516))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.69/2.56  tff(c_7745, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3' | ~v5_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_7737])).
% 7.69/2.56  tff(c_7753, plain, (k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_5707, c_7745])).
% 7.69/2.56  tff(c_5896, plain, (![B_417, A_418]: (r1_tarski(B_417, k2_pre_topc(A_418, B_417)) | ~m1_subset_1(B_417, k1_zfmisc_1(u1_struct_0(A_418))) | ~l1_pre_topc(A_418))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.69/2.56  tff(c_5900, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_5896])).
% 7.69/2.56  tff(c_5906, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_5900])).
% 7.69/2.56  tff(c_5916, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3' | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_5906, c_2])).
% 7.69/2.56  tff(c_7692, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_5916])).
% 7.69/2.56  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(k2_pre_topc(A_3, B_4), k1_zfmisc_1(u1_struct_0(A_3))) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0(A_3))) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.69/2.56  tff(c_7711, plain, (![A_514, B_515]: (k2_pre_topc(A_514, k2_pre_topc(A_514, B_515))=k2_pre_topc(A_514, B_515) | ~m1_subset_1(B_515, k1_zfmisc_1(u1_struct_0(A_514))) | ~l1_pre_topc(A_514))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.69/2.56  tff(c_7719, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))=k2_pre_topc('#skF_1', '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_7711])).
% 7.69/2.56  tff(c_7727, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))=k2_pre_topc('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_7719])).
% 7.69/2.56  tff(c_7809, plain, (![A_522, B_523]: (r1_tarski(k1_tops_1(A_522, k2_pre_topc(A_522, B_523)), B_523) | ~v4_tops_1(B_523, A_522) | ~m1_subset_1(B_523, k1_zfmisc_1(u1_struct_0(A_522))) | ~l1_pre_topc(A_522))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.69/2.56  tff(c_7820, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')), k2_pre_topc('#skF_1', '#skF_3')) | ~v4_tops_1(k2_pre_topc('#skF_1', '#skF_3'), '#skF_1') | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_7727, c_7809])).
% 7.69/2.56  tff(c_7830, plain, (r1_tarski(k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3')), k2_pre_topc('#skF_1', '#skF_3')) | ~v4_tops_1(k2_pre_topc('#skF_1', '#skF_3'), '#skF_1') | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_7820])).
% 7.69/2.56  tff(c_7929, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_7830])).
% 7.69/2.56  tff(c_7932, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_7929])).
% 7.69/2.56  tff(c_7936, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_7932])).
% 7.69/2.56  tff(c_7938, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_7830])).
% 7.69/2.56  tff(c_8074, plain, (![A_538, B_539, C_540]: (r1_tarski(k2_pre_topc(A_538, B_539), k2_pre_topc(A_538, C_540)) | ~r1_tarski(B_539, C_540) | ~m1_subset_1(C_540, k1_zfmisc_1(u1_struct_0(A_538))) | ~m1_subset_1(B_539, k1_zfmisc_1(u1_struct_0(A_538))) | ~l1_pre_topc(A_538))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.69/2.56  tff(c_8097, plain, (![C_540]: (r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', C_540)) | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), C_540) | ~m1_subset_1(C_540, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_7727, c_8074])).
% 7.69/2.56  tff(c_8257, plain, (![C_544]: (r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', C_544)) | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), C_544) | ~m1_subset_1(C_544, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_7938, c_8097])).
% 7.69/2.56  tff(c_8269, plain, (r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), '#skF_3') | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), k1_tops_1('#skF_1', '#skF_3')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_7753, c_8257])).
% 7.69/2.56  tff(c_8277, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), k1_tops_1('#skF_1', '#skF_3')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_7692, c_8269])).
% 7.69/2.56  tff(c_8280, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_8277])).
% 7.69/2.56  tff(c_8283, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_8280])).
% 7.69/2.56  tff(c_8287, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_8283])).
% 7.69/2.56  tff(c_8289, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_8277])).
% 7.69/2.56  tff(c_10, plain, (![A_5, B_6]: (k2_pre_topc(A_5, k2_pre_topc(A_5, B_6))=k2_pre_topc(A_5, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.69/2.56  tff(c_8293, plain, (k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3')))=k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8289, c_10])).
% 7.69/2.56  tff(c_8303, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_7753, c_7753, c_8293])).
% 7.69/2.56  tff(c_8346, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8303, c_7692])).
% 7.69/2.56  tff(c_8355, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_8346])).
% 7.69/2.56  tff(c_8356, plain, (k2_pre_topc('#skF_1', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_5916])).
% 7.69/2.56  tff(c_8926, plain, (![B_586, A_587]: (v4_tops_1(B_586, A_587) | ~r1_tarski(B_586, k2_pre_topc(A_587, k1_tops_1(A_587, B_586))) | ~r1_tarski(k1_tops_1(A_587, k2_pre_topc(A_587, B_586)), B_586) | ~m1_subset_1(B_586, k1_zfmisc_1(u1_struct_0(A_587))) | ~l1_pre_topc(A_587))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.69/2.56  tff(c_8941, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8356, c_8926])).
% 7.69/2.56  tff(c_8953, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_8462, c_6, c_8421, c_8941])).
% 7.69/2.56  tff(c_8955, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5893, c_8953])).
% 7.69/2.56  tff(c_8957, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_5892])).
% 7.69/2.56  tff(c_5708, plain, (v5_tops_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 7.69/2.56  tff(c_44, plain, (~v5_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.69/2.56  tff(c_8961, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5890, c_8957, c_5708, c_44])).
% 7.69/2.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.69/2.56  
% 7.69/2.56  Inference rules
% 7.69/2.56  ----------------------
% 7.69/2.56  #Ref     : 0
% 7.69/2.56  #Sup     : 1876
% 7.69/2.56  #Fact    : 0
% 7.69/2.56  #Define  : 0
% 7.69/2.56  #Split   : 130
% 7.69/2.56  #Chain   : 0
% 7.69/2.56  #Close   : 0
% 7.69/2.56  
% 7.69/2.56  Ordering : KBO
% 7.69/2.56  
% 7.69/2.56  Simplification rules
% 7.69/2.56  ----------------------
% 7.69/2.56  #Subsume      : 162
% 7.69/2.56  #Demod        : 2846
% 7.69/2.56  #Tautology    : 855
% 7.69/2.56  #SimpNegUnit  : 20
% 7.69/2.56  #BackRed      : 104
% 7.69/2.56  
% 7.69/2.56  #Partial instantiations: 0
% 7.69/2.56  #Strategies tried      : 1
% 7.69/2.56  
% 7.69/2.56  Timing (in seconds)
% 7.69/2.56  ----------------------
% 7.69/2.56  Preprocessing        : 0.32
% 7.69/2.56  Parsing              : 0.18
% 7.69/2.56  CNF conversion       : 0.02
% 7.69/2.56  Main loop            : 1.43
% 7.69/2.56  Inferencing          : 0.47
% 7.69/2.56  Reduction            : 0.53
% 7.69/2.56  Demodulation         : 0.38
% 7.69/2.56  BG Simplification    : 0.06
% 7.69/2.56  Subsumption          : 0.28
% 7.69/2.57  Abstraction          : 0.07
% 7.69/2.57  MUC search           : 0.00
% 7.69/2.57  Cooper               : 0.00
% 7.69/2.57  Total                : 1.82
% 7.69/2.57  Index Insertion      : 0.00
% 7.69/2.57  Index Deletion       : 0.00
% 7.69/2.57  Index Matching       : 0.00
% 7.69/2.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
