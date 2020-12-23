%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:21 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 154 expanded)
%              Number of leaves         :   24 (  65 expanded)
%              Depth                    :    8
%              Number of atoms          :  142 ( 418 expanded)
%              Number of equality atoms :   26 (  41 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_tops_1 > v5_tops_1 > v4_pre_topc > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v6_tops_1,type,(
    v6_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v3_pre_topc(B,A)
                & v4_pre_topc(B,A) )
             => ( v5_tops_1(B,A)
              <=> v6_tops_1(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_tops_1)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_tops_1(B,A)
          <=> B = k1_tops_1(A,k2_pre_topc(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tops_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_85,axiom,(
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

tff(c_32,plain,
    ( ~ v6_tops_1('#skF_2','#skF_1')
    | ~ v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_41,plain,(
    ~ v5_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_24,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_110,plain,(
    ! [A_40,B_41] :
      ( k2_pre_topc(A_40,B_41) = B_41
      | ~ v4_pre_topc(B_41,A_40)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_113,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_110])).

tff(c_116,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24,c_113])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,
    ( v5_tops_1('#skF_2','#skF_1')
    | v6_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_42,plain,(
    v6_tops_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_38])).

tff(c_60,plain,(
    ! [A_28,B_29] :
      ( k2_pre_topc(A_28,B_29) = B_29
      | ~ v4_pre_topc(B_29,A_28)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_63,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_60])).

tff(c_66,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24,c_63])).

tff(c_90,plain,(
    ! [A_38,B_39] :
      ( k1_tops_1(A_38,k2_pre_topc(A_38,B_39)) = B_39
      | ~ v6_tops_1(B_39,A_38)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_92,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = '#skF_2'
    | ~ v6_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_90])).

tff(c_95,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_42,c_66,c_92])).

tff(c_50,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(k1_tops_1(A_26,B_27),B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_52,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_50])).

tff(c_55,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_52])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_55,c_2])).

tff(c_59,plain,(
    ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_96,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_59])).

tff(c_100,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_96])).

tff(c_101,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_132,plain,(
    ! [B_46,A_47] :
      ( v5_tops_1(B_46,A_47)
      | k2_pre_topc(A_47,k1_tops_1(A_47,B_46)) != B_46
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_134,plain,
    ( v5_tops_1('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_132])).

tff(c_136,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_116,c_134])).

tff(c_138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_136])).

tff(c_139,plain,(
    ~ v6_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_150,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(k1_tops_1(A_50,B_51),B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_152,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_150])).

tff(c_155,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_152])).

tff(c_158,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_155,c_2])).

tff(c_159,plain,(
    ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_26,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_211,plain,(
    ! [B_64,A_65,C_66] :
      ( r1_tarski(B_64,k1_tops_1(A_65,C_66))
      | ~ r1_tarski(B_64,C_66)
      | ~ v3_pre_topc(B_64,A_65)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_213,plain,(
    ! [B_64] :
      ( r1_tarski(B_64,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_64,'#skF_2')
      | ~ v3_pre_topc(B_64,'#skF_1')
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_211])).

tff(c_218,plain,(
    ! [B_67] :
      ( r1_tarski(B_67,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_67,'#skF_2')
      | ~ v3_pre_topc(B_67,'#skF_1')
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_213])).

tff(c_221,plain,
    ( r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_218])).

tff(c_224,plain,(
    r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_6,c_221])).

tff(c_226,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_159,c_224])).

tff(c_227,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_236,plain,(
    ! [A_68,B_69] :
      ( k2_pre_topc(A_68,B_69) = B_69
      | ~ v4_pre_topc(B_69,A_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_239,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_236])).

tff(c_242,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24,c_239])).

tff(c_254,plain,(
    ! [B_72,A_73] :
      ( v6_tops_1(B_72,A_73)
      | k1_tops_1(A_73,k2_pre_topc(A_73,B_72)) != B_72
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_256,plain,
    ( v6_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_254])).

tff(c_258,plain,(
    v6_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_227,c_256])).

tff(c_260,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_258])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:41:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.41  
% 2.29/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.41  %$ v6_tops_1 > v5_tops_1 > v4_pre_topc > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.29/1.41  
% 2.29/1.41  %Foreground sorts:
% 2.29/1.41  
% 2.29/1.41  
% 2.29/1.41  %Background operators:
% 2.29/1.41  
% 2.29/1.41  
% 2.29/1.41  %Foreground operators:
% 2.29/1.41  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.29/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.41  tff(v6_tops_1, type, v6_tops_1: ($i * $i) > $o).
% 2.29/1.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.29/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.29/1.41  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.29/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.29/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.29/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.29/1.41  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.29/1.41  tff(v5_tops_1, type, v5_tops_1: ($i * $i) > $o).
% 2.29/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.41  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.29/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.29/1.41  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.29/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.29/1.41  
% 2.29/1.43  tff(f_99, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v4_pre_topc(B, A)) => (v5_tops_1(B, A) <=> v6_tops_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_tops_1)).
% 2.29/1.43  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.29/1.43  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.29/1.43  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_tops_1(B, A) <=> (B = k1_tops_1(A, k2_pre_topc(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_tops_1)).
% 2.29/1.43  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 2.29/1.43  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v5_tops_1(B, A) <=> (B = k2_pre_topc(A, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tops_1)).
% 2.29/1.43  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 2.29/1.43  tff(c_32, plain, (~v6_tops_1('#skF_2', '#skF_1') | ~v5_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.29/1.43  tff(c_41, plain, (~v5_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_32])).
% 2.29/1.43  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.29/1.43  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.29/1.43  tff(c_24, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.29/1.43  tff(c_110, plain, (![A_40, B_41]: (k2_pre_topc(A_40, B_41)=B_41 | ~v4_pre_topc(B_41, A_40) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_40))) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.29/1.43  tff(c_113, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_110])).
% 2.29/1.43  tff(c_116, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_24, c_113])).
% 2.29/1.43  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.29/1.43  tff(c_38, plain, (v5_tops_1('#skF_2', '#skF_1') | v6_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.29/1.43  tff(c_42, plain, (v6_tops_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_41, c_38])).
% 2.29/1.43  tff(c_60, plain, (![A_28, B_29]: (k2_pre_topc(A_28, B_29)=B_29 | ~v4_pre_topc(B_29, A_28) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.29/1.43  tff(c_63, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_60])).
% 2.29/1.43  tff(c_66, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_24, c_63])).
% 2.29/1.43  tff(c_90, plain, (![A_38, B_39]: (k1_tops_1(A_38, k2_pre_topc(A_38, B_39))=B_39 | ~v6_tops_1(B_39, A_38) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.29/1.43  tff(c_92, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))='#skF_2' | ~v6_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_90])).
% 2.29/1.43  tff(c_95, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_42, c_66, c_92])).
% 2.29/1.43  tff(c_50, plain, (![A_26, B_27]: (r1_tarski(k1_tops_1(A_26, B_27), B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.29/1.43  tff(c_52, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_50])).
% 2.29/1.43  tff(c_55, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_52])).
% 2.29/1.43  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.29/1.43  tff(c_58, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_55, c_2])).
% 2.29/1.43  tff(c_59, plain, (~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_58])).
% 2.29/1.43  tff(c_96, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_59])).
% 2.29/1.43  tff(c_100, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_96])).
% 2.29/1.43  tff(c_101, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_58])).
% 2.29/1.43  tff(c_132, plain, (![B_46, A_47]: (v5_tops_1(B_46, A_47) | k2_pre_topc(A_47, k1_tops_1(A_47, B_46))!=B_46 | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.29/1.43  tff(c_134, plain, (v5_tops_1('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_101, c_132])).
% 2.29/1.43  tff(c_136, plain, (v5_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_116, c_134])).
% 2.29/1.43  tff(c_138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41, c_136])).
% 2.29/1.43  tff(c_139, plain, (~v6_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_32])).
% 2.29/1.43  tff(c_150, plain, (![A_50, B_51]: (r1_tarski(k1_tops_1(A_50, B_51), B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.29/1.43  tff(c_152, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_150])).
% 2.29/1.43  tff(c_155, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_152])).
% 2.29/1.43  tff(c_158, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_155, c_2])).
% 2.29/1.43  tff(c_159, plain, (~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_158])).
% 2.29/1.43  tff(c_26, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.29/1.43  tff(c_211, plain, (![B_64, A_65, C_66]: (r1_tarski(B_64, k1_tops_1(A_65, C_66)) | ~r1_tarski(B_64, C_66) | ~v3_pre_topc(B_64, A_65) | ~m1_subset_1(C_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.29/1.43  tff(c_213, plain, (![B_64]: (r1_tarski(B_64, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_64, '#skF_2') | ~v3_pre_topc(B_64, '#skF_1') | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_211])).
% 2.29/1.43  tff(c_218, plain, (![B_67]: (r1_tarski(B_67, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_67, '#skF_2') | ~v3_pre_topc(B_67, '#skF_1') | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_213])).
% 2.29/1.43  tff(c_221, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_218])).
% 2.29/1.43  tff(c_224, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_6, c_221])).
% 2.29/1.43  tff(c_226, plain, $false, inference(negUnitSimplification, [status(thm)], [c_159, c_224])).
% 2.29/1.43  tff(c_227, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_158])).
% 2.29/1.43  tff(c_236, plain, (![A_68, B_69]: (k2_pre_topc(A_68, B_69)=B_69 | ~v4_pre_topc(B_69, A_68) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.29/1.43  tff(c_239, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_236])).
% 2.29/1.43  tff(c_242, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_24, c_239])).
% 2.29/1.43  tff(c_254, plain, (![B_72, A_73]: (v6_tops_1(B_72, A_73) | k1_tops_1(A_73, k2_pre_topc(A_73, B_72))!=B_72 | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.29/1.43  tff(c_256, plain, (v6_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_242, c_254])).
% 2.29/1.43  tff(c_258, plain, (v6_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_227, c_256])).
% 2.29/1.43  tff(c_260, plain, $false, inference(negUnitSimplification, [status(thm)], [c_139, c_258])).
% 2.29/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.43  
% 2.29/1.43  Inference rules
% 2.29/1.43  ----------------------
% 2.29/1.43  #Ref     : 0
% 2.29/1.43  #Sup     : 41
% 2.29/1.43  #Fact    : 0
% 2.29/1.43  #Define  : 0
% 2.29/1.43  #Split   : 4
% 2.29/1.43  #Chain   : 0
% 2.29/1.43  #Close   : 0
% 2.29/1.43  
% 2.29/1.43  Ordering : KBO
% 2.29/1.43  
% 2.29/1.43  Simplification rules
% 2.29/1.43  ----------------------
% 2.29/1.43  #Subsume      : 3
% 2.29/1.43  #Demod        : 67
% 2.29/1.43  #Tautology    : 30
% 2.29/1.43  #SimpNegUnit  : 6
% 2.29/1.43  #BackRed      : 4
% 2.29/1.43  
% 2.29/1.43  #Partial instantiations: 0
% 2.29/1.43  #Strategies tried      : 1
% 2.29/1.43  
% 2.29/1.43  Timing (in seconds)
% 2.29/1.43  ----------------------
% 2.29/1.44  Preprocessing        : 0.37
% 2.29/1.44  Parsing              : 0.19
% 2.29/1.44  CNF conversion       : 0.04
% 2.29/1.44  Main loop            : 0.22
% 2.29/1.44  Inferencing          : 0.09
% 2.29/1.44  Reduction            : 0.07
% 2.29/1.44  Demodulation         : 0.05
% 2.29/1.44  BG Simplification    : 0.02
% 2.29/1.44  Subsumption          : 0.04
% 2.29/1.44  Abstraction          : 0.01
% 2.29/1.44  MUC search           : 0.00
% 2.29/1.44  Cooper               : 0.00
% 2.29/1.44  Total                : 0.64
% 2.29/1.44  Index Insertion      : 0.00
% 2.29/1.44  Index Deletion       : 0.00
% 2.29/1.44  Index Matching       : 0.00
% 2.29/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
