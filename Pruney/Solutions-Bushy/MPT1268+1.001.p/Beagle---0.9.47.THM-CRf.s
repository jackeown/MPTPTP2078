%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1268+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:41 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 218 expanded)
%              Number of leaves         :   25 (  87 expanded)
%              Depth                    :   14
%              Number of atoms          :  247 ( 834 expanded)
%              Number of equality atoms :   21 (  86 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > v1_tops_1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( C != k1_xboole_0
                    & v3_pre_topc(C,A)
                    & r1_xboole_0(B,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_tops_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,k3_subset_1(A,C))
          <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

tff(f_33,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

tff(c_30,plain,
    ( k1_xboole_0 != '#skF_4'
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_49,plain,(
    ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_28,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_26,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(k3_subset_1(A_4,B_5),k1_zfmisc_1(A_4))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ! [A_12,B_18] :
      ( m1_subset_1('#skF_1'(A_12,B_18),k1_zfmisc_1(u1_struct_0(A_12)))
      | v1_tops_1(B_18,A_12)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_104,plain,(
    ! [B_50,A_51] :
      ( r1_xboole_0(B_50,'#skF_1'(A_51,B_50))
      | v1_tops_1(B_50,A_51)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_206,plain,(
    ! [A_74,B_75] :
      ( r1_xboole_0(k3_subset_1(u1_struct_0(A_74),B_75),'#skF_1'(A_74,k3_subset_1(u1_struct_0(A_74),B_75)))
      | v1_tops_1(k3_subset_1(u1_struct_0(A_74),B_75),A_74)
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74))) ) ),
    inference(resolution,[status(thm)],[c_6,c_104])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( r1_xboole_0(B_7,A_6)
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_225,plain,(
    ! [A_82,B_83] :
      ( r1_xboole_0('#skF_1'(A_82,k3_subset_1(u1_struct_0(A_82),B_83)),k3_subset_1(u1_struct_0(A_82),B_83))
      | v1_tops_1(k3_subset_1(u1_struct_0(A_82),B_83),A_82)
      | ~ l1_pre_topc(A_82)
      | ~ v2_pre_topc(A_82)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82))) ) ),
    inference(resolution,[status(thm)],[c_206,c_8])).

tff(c_12,plain,(
    ! [B_9,C_11,A_8] :
      ( r1_tarski(B_9,C_11)
      | ~ r1_xboole_0(B_9,k3_subset_1(A_8,C_11))
      | ~ m1_subset_1(C_11,k1_zfmisc_1(A_8))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_268,plain,(
    ! [A_105,B_106] :
      ( r1_tarski('#skF_1'(A_105,k3_subset_1(u1_struct_0(A_105),B_106)),B_106)
      | ~ m1_subset_1('#skF_1'(A_105,k3_subset_1(u1_struct_0(A_105),B_106)),k1_zfmisc_1(u1_struct_0(A_105)))
      | v1_tops_1(k3_subset_1(u1_struct_0(A_105),B_106),A_105)
      | ~ l1_pre_topc(A_105)
      | ~ v2_pre_topc(A_105)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105))) ) ),
    inference(resolution,[status(thm)],[c_225,c_12])).

tff(c_273,plain,(
    ! [A_107,B_108] :
      ( r1_tarski('#skF_1'(A_107,k3_subset_1(u1_struct_0(A_107),B_108)),B_108)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_107)))
      | v1_tops_1(k3_subset_1(u1_struct_0(A_107),B_108),A_107)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_107),B_108),k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107)
      | ~ v2_pre_topc(A_107) ) ),
    inference(resolution,[status(thm)],[c_22,c_268])).

tff(c_278,plain,(
    ! [A_109,B_110] :
      ( r1_tarski('#skF_1'(A_109,k3_subset_1(u1_struct_0(A_109),B_110)),B_110)
      | v1_tops_1(k3_subset_1(u1_struct_0(A_109),B_110),A_109)
      | ~ l1_pre_topc(A_109)
      | ~ v2_pre_topc(A_109)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_109))) ) ),
    inference(resolution,[status(thm)],[c_6,c_273])).

tff(c_115,plain,(
    ! [A_52,B_53] :
      ( v3_pre_topc('#skF_1'(A_52,B_53),A_52)
      | v1_tops_1(B_53,A_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52)
      | ~ v2_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_121,plain,(
    ! [A_52,B_5] :
      ( v3_pre_topc('#skF_1'(A_52,k3_subset_1(u1_struct_0(A_52),B_5)),A_52)
      | v1_tops_1(k3_subset_1(u1_struct_0(A_52),B_5),A_52)
      | ~ l1_pre_topc(A_52)
      | ~ v2_pre_topc(A_52)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0(A_52))) ) ),
    inference(resolution,[status(thm)],[c_6,c_115])).

tff(c_125,plain,(
    ! [A_54,B_55] :
      ( m1_subset_1('#skF_1'(A_54,B_55),k1_zfmisc_1(u1_struct_0(A_54)))
      | v1_tops_1(B_55,A_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54)
      | ~ v2_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_48,plain,(
    ! [C_29] :
      ( v2_tops_1('#skF_3','#skF_2')
      | k1_xboole_0 = C_29
      | ~ v3_pre_topc(C_29,'#skF_2')
      | ~ r1_tarski(C_29,'#skF_3')
      | ~ m1_subset_1(C_29,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_70,plain,(
    ! [C_29] :
      ( k1_xboole_0 = C_29
      | ~ v3_pre_topc(C_29,'#skF_2')
      | ~ r1_tarski(C_29,'#skF_3')
      | ~ m1_subset_1(C_29,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_48])).

tff(c_133,plain,(
    ! [B_55] :
      ( '#skF_1'('#skF_2',B_55) = k1_xboole_0
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_55),'#skF_2')
      | ~ r1_tarski('#skF_1'('#skF_2',B_55),'#skF_3')
      | v1_tops_1(B_55,'#skF_2')
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_125,c_70])).

tff(c_157,plain,(
    ! [B_64] :
      ( '#skF_1'('#skF_2',B_64) = k1_xboole_0
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_64),'#skF_2')
      | ~ r1_tarski('#skF_1'('#skF_2',B_64),'#skF_3')
      | v1_tops_1(B_64,'#skF_2')
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_133])).

tff(c_177,plain,(
    ! [B_67] :
      ( '#skF_1'('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),B_67)) = k1_xboole_0
      | ~ v3_pre_topc('#skF_1'('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),B_67)),'#skF_2')
      | ~ r1_tarski('#skF_1'('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),B_67)),'#skF_3')
      | v1_tops_1(k3_subset_1(u1_struct_0('#skF_2'),B_67),'#skF_2')
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_6,c_157])).

tff(c_181,plain,(
    ! [B_5] :
      ( '#skF_1'('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),B_5)) = k1_xboole_0
      | ~ r1_tarski('#skF_1'('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),B_5)),'#skF_3')
      | v1_tops_1(k3_subset_1(u1_struct_0('#skF_2'),B_5),'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_121,c_177])).

tff(c_184,plain,(
    ! [B_5] :
      ( '#skF_1'('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),B_5)) = k1_xboole_0
      | ~ r1_tarski('#skF_1'('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),B_5)),'#skF_3')
      | v1_tops_1(k3_subset_1(u1_struct_0('#skF_2'),B_5),'#skF_2')
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_181])).

tff(c_282,plain,
    ( '#skF_1'('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k1_xboole_0
    | v1_tops_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_278,c_184])).

tff(c_285,plain,
    ( '#skF_1'('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k1_xboole_0
    | v1_tops_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28,c_26,c_282])).

tff(c_286,plain,(
    v1_tops_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_285])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v2_tops_1(B_3,A_1)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(A_1),B_3),A_1)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_289,plain,
    ( v2_tops_1('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_286,c_2])).

tff(c_292,plain,(
    v2_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_289])).

tff(c_294,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_292])).

tff(c_295,plain,(
    '#skF_1'('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_285])).

tff(c_56,plain,(
    ! [A_39,B_40] :
      ( '#skF_1'(A_39,B_40) != k1_xboole_0
      | v1_tops_1(B_40,A_39)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39)
      | ~ v2_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_143,plain,(
    ! [A_56,B_57] :
      ( '#skF_1'(A_56,k3_subset_1(u1_struct_0(A_56),B_57)) != k1_xboole_0
      | v1_tops_1(k3_subset_1(u1_struct_0(A_56),B_57),A_56)
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56))) ) ),
    inference(resolution,[status(thm)],[c_6,c_56])).

tff(c_147,plain,(
    ! [B_57,A_56] :
      ( v2_tops_1(B_57,A_56)
      | '#skF_1'(A_56,k3_subset_1(u1_struct_0(A_56),B_57)) != k1_xboole_0
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56))) ) ),
    inference(resolution,[status(thm)],[c_143,c_2])).

tff(c_350,plain,
    ( v2_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_147])).

tff(c_396,plain,(
    v2_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28,c_26,c_350])).

tff(c_398,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_396])).

tff(c_400,plain,(
    v2_tops_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_34,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_402,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_34])).

tff(c_4,plain,(
    ! [A_1,B_3] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_1),B_3),A_1)
      | ~ v2_tops_1(B_3,A_1)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_36,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_407,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_36])).

tff(c_399,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_32,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_404,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_32])).

tff(c_434,plain,(
    ! [B_122,A_123,C_124] :
      ( r1_xboole_0(B_122,k3_subset_1(A_123,C_124))
      | ~ r1_tarski(B_122,C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(A_123))
      | ~ m1_subset_1(B_122,k1_zfmisc_1(A_123)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_441,plain,(
    ! [A_123,C_124,B_122] :
      ( r1_xboole_0(k3_subset_1(A_123,C_124),B_122)
      | ~ r1_tarski(B_122,C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(A_123))
      | ~ m1_subset_1(B_122,k1_zfmisc_1(A_123)) ) ),
    inference(resolution,[status(thm)],[c_434,c_8])).

tff(c_500,plain,(
    ! [B_136,C_137,A_138] :
      ( ~ r1_xboole_0(B_136,C_137)
      | ~ v3_pre_topc(C_137,A_138)
      | k1_xboole_0 = C_137
      | ~ m1_subset_1(C_137,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ v1_tops_1(B_136,A_138)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_589,plain,(
    ! [B_181,A_182,A_183,C_184] :
      ( ~ v3_pre_topc(B_181,A_182)
      | k1_xboole_0 = B_181
      | ~ m1_subset_1(B_181,k1_zfmisc_1(u1_struct_0(A_182)))
      | ~ v1_tops_1(k3_subset_1(A_183,C_184),A_182)
      | ~ m1_subset_1(k3_subset_1(A_183,C_184),k1_zfmisc_1(u1_struct_0(A_182)))
      | ~ l1_pre_topc(A_182)
      | ~ v2_pre_topc(A_182)
      | ~ r1_tarski(B_181,C_184)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(A_183))
      | ~ m1_subset_1(B_181,k1_zfmisc_1(A_183)) ) ),
    inference(resolution,[status(thm)],[c_441,c_500])).

tff(c_596,plain,(
    ! [A_183,C_184] :
      ( ~ v3_pre_topc('#skF_4','#skF_2')
      | k1_xboole_0 = '#skF_4'
      | ~ v1_tops_1(k3_subset_1(A_183,C_184),'#skF_2')
      | ~ m1_subset_1(k3_subset_1(A_183,C_184),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ r1_tarski('#skF_4',C_184)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(A_183))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_183)) ) ),
    inference(resolution,[status(thm)],[c_407,c_589])).

tff(c_603,plain,(
    ! [A_183,C_184] :
      ( k1_xboole_0 = '#skF_4'
      | ~ v1_tops_1(k3_subset_1(A_183,C_184),'#skF_2')
      | ~ m1_subset_1(k3_subset_1(A_183,C_184),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski('#skF_4',C_184)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(A_183))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_183)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_404,c_596])).

tff(c_614,plain,(
    ! [A_188,C_189] :
      ( ~ v1_tops_1(k3_subset_1(A_188,C_189),'#skF_2')
      | ~ m1_subset_1(k3_subset_1(A_188,C_189),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski('#skF_4',C_189)
      | ~ m1_subset_1(C_189,k1_zfmisc_1(A_188))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_188)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_399,c_603])).

tff(c_618,plain,(
    ! [B_5] :
      ( ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_2'),B_5),'#skF_2')
      | ~ r1_tarski('#skF_4',B_5)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_6,c_614])).

tff(c_622,plain,(
    ! [B_190] :
      ( ~ v1_tops_1(k3_subset_1(u1_struct_0('#skF_2'),B_190),'#skF_2')
      | ~ r1_tarski('#skF_4',B_190)
      | ~ m1_subset_1(B_190,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_618])).

tff(c_630,plain,(
    ! [B_3] :
      ( ~ r1_tarski('#skF_4',B_3)
      | ~ v2_tops_1(B_3,'#skF_2')
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_4,c_622])).

tff(c_637,plain,(
    ! [B_191] :
      ( ~ r1_tarski('#skF_4',B_191)
      | ~ v2_tops_1(B_191,'#skF_2')
      | ~ m1_subset_1(B_191,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_630])).

tff(c_651,plain,
    ( ~ r1_tarski('#skF_4','#skF_3')
    | ~ v2_tops_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_637])).

tff(c_660,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_402,c_651])).

%------------------------------------------------------------------------------
