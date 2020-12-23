%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:27 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 264 expanded)
%              Number of leaves         :   38 ( 104 expanded)
%              Depth                    :   12
%              Number of atoms          :  155 ( 762 expanded)
%              Number of equality atoms :   12 (  95 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

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

tff(f_134,negated_conjecture,(
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

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_71,axiom,(
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

tff(f_85,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_100,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc7_pre_topc)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_106,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_30,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_32,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_34,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_56,plain,(
    ! [A_1] : r1_tarski('#skF_5',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_42,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_40,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_57,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2])).

tff(c_18,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_1'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_53,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_1'(A_11),A_11)
      | A_11 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_18])).

tff(c_24,plain,(
    ! [A_35] :
      ( v4_pre_topc(k2_struct_0(A_35),A_35)
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_22,plain,(
    ! [A_34] :
      ( l1_struct_0(A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_74,plain,(
    ! [A_55] :
      ( u1_struct_0(A_55) = k2_struct_0(A_55)
      | ~ l1_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_85,plain,(
    ! [A_59] :
      ( u1_struct_0(A_59) = k2_struct_0(A_59)
      | ~ l1_pre_topc(A_59) ) ),
    inference(resolution,[status(thm)],[c_22,c_74])).

tff(c_89,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_85])).

tff(c_168,plain,(
    ! [A_78] :
      ( m1_subset_1('#skF_2'(A_78),k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78)
      | ~ v2_pre_topc(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_173,plain,
    ( m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_168])).

tff(c_176,plain,
    ( m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_173])).

tff(c_177,plain,(
    m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_176])).

tff(c_12,plain,(
    ! [C_8,B_7,A_6] :
      ( ~ v1_xboole_0(C_8)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(C_8))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_191,plain,(
    ! [A_6] :
      ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ r2_hidden(A_6,'#skF_2'('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_177,c_12])).

tff(c_193,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_191])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_92,plain,(
    m1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_38])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_32,plain,(
    ! [A_38] :
      ( v3_pre_topc(k2_struct_0(A_38),A_38)
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_6,plain,(
    ! [A_2] : k2_subset_1(A_2) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_8,plain,(
    ! [A_3] : m1_subset_1(k2_subset_1(A_3),k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_55,plain,(
    ! [A_3] : m1_subset_1(A_3,k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_52,plain,(
    ! [D_50] :
      ( v3_pre_topc(D_50,'#skF_3')
      | ~ r2_hidden(D_50,'#skF_5')
      | ~ m1_subset_1(D_50,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_105,plain,(
    ! [D_62] :
      ( v3_pre_topc(D_62,'#skF_3')
      | ~ r2_hidden(D_62,'#skF_5')
      | ~ m1_subset_1(D_62,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_52])).

tff(c_110,plain,
    ( v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ r2_hidden(k2_struct_0('#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_55,c_105])).

tff(c_123,plain,(
    ~ r2_hidden(k2_struct_0('#skF_3'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_46,plain,(
    ! [D_50] :
      ( r2_hidden(D_50,'#skF_5')
      | ~ r2_hidden('#skF_4',D_50)
      | ~ v4_pre_topc(D_50,'#skF_3')
      | ~ v3_pre_topc(D_50,'#skF_3')
      | ~ m1_subset_1(D_50,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_195,plain,(
    ! [D_79] :
      ( r2_hidden(D_79,'#skF_5')
      | ~ r2_hidden('#skF_4',D_79)
      | ~ v4_pre_topc(D_79,'#skF_3')
      | ~ v3_pre_topc(D_79,'#skF_3')
      | ~ m1_subset_1(D_79,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_46])).

tff(c_202,plain,
    ( r2_hidden(k2_struct_0('#skF_3'),'#skF_5')
    | ~ r2_hidden('#skF_4',k2_struct_0('#skF_3'))
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_55,c_195])).

tff(c_206,plain,
    ( ~ r2_hidden('#skF_4',k2_struct_0('#skF_3'))
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_202])).

tff(c_213,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_206])).

tff(c_225,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_213])).

tff(c_229,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_225])).

tff(c_230,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ r2_hidden('#skF_4',k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_232,plain,(
    ~ r2_hidden('#skF_4',k2_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_230])).

tff(c_237,plain,
    ( v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_10,c_232])).

tff(c_240,plain,(
    v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_237])).

tff(c_242,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_240])).

tff(c_243,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_230])).

tff(c_255,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_243])).

tff(c_259,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_255])).

tff(c_326,plain,(
    ! [A_87] : ~ r2_hidden(A_87,'#skF_2'('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_191])).

tff(c_336,plain,(
    '#skF_2'('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_53,c_326])).

tff(c_28,plain,(
    ! [A_36] :
      ( ~ v1_xboole_0('#skF_2'(A_36))
      | ~ l1_pre_topc(A_36)
      | ~ v2_pre_topc(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_349,plain,
    ( ~ v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_28])).

tff(c_359,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_57,c_349])).

tff(c_361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_359])).

tff(c_363,plain,(
    r2_hidden(k2_struct_0('#skF_3'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_14,plain,(
    ! [B_10,A_9] :
      ( ~ r1_tarski(B_10,A_9)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_367,plain,(
    ~ r1_tarski('#skF_5',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_363,c_14])).

tff(c_371,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_367])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:54:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.28  
% 2.34/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.29  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 2.34/1.29  
% 2.34/1.29  %Foreground sorts:
% 2.34/1.29  
% 2.34/1.29  
% 2.34/1.29  %Background operators:
% 2.34/1.29  
% 2.34/1.29  
% 2.34/1.29  %Foreground operators:
% 2.34/1.29  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.34/1.29  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.34/1.29  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.34/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.34/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.34/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.34/1.29  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.34/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.34/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.34/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.34/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.34/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.34/1.29  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.34/1.29  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.34/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.34/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.29  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.34/1.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.34/1.29  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.34/1.29  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.34/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.34/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.34/1.29  
% 2.34/1.30  tff(f_134, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.34/1.30  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.34/1.30  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.34/1.30  tff(f_71, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 2.34/1.30  tff(f_85, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.34/1.30  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.34/1.30  tff(f_75, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.34/1.30  tff(f_100, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc7_pre_topc)).
% 2.34/1.30  tff(f_45, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.34/1.30  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.34/1.30  tff(f_106, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 2.34/1.30  tff(f_30, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.34/1.30  tff(f_32, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.34/1.30  tff(f_50, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.34/1.30  tff(c_34, plain, (k1_xboole_0='#skF_5'), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.34/1.30  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.34/1.30  tff(c_56, plain, (![A_1]: (r1_tarski('#skF_5', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_4])).
% 2.34/1.30  tff(c_44, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.34/1.30  tff(c_42, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.34/1.30  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.34/1.30  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.34/1.30  tff(c_57, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2])).
% 2.34/1.30  tff(c_18, plain, (![A_11]: (r2_hidden('#skF_1'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.34/1.30  tff(c_53, plain, (![A_11]: (r2_hidden('#skF_1'(A_11), A_11) | A_11='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_18])).
% 2.34/1.30  tff(c_24, plain, (![A_35]: (v4_pre_topc(k2_struct_0(A_35), A_35) | ~l1_pre_topc(A_35) | ~v2_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.34/1.30  tff(c_22, plain, (![A_34]: (l1_struct_0(A_34) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.34/1.30  tff(c_74, plain, (![A_55]: (u1_struct_0(A_55)=k2_struct_0(A_55) | ~l1_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.34/1.30  tff(c_85, plain, (![A_59]: (u1_struct_0(A_59)=k2_struct_0(A_59) | ~l1_pre_topc(A_59))), inference(resolution, [status(thm)], [c_22, c_74])).
% 2.34/1.30  tff(c_89, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_85])).
% 2.34/1.30  tff(c_168, plain, (![A_78]: (m1_subset_1('#skF_2'(A_78), k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78) | ~v2_pre_topc(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.34/1.30  tff(c_173, plain, (m1_subset_1('#skF_2'('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_89, c_168])).
% 2.34/1.30  tff(c_176, plain, (m1_subset_1('#skF_2'('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_173])).
% 2.34/1.30  tff(c_177, plain, (m1_subset_1('#skF_2'('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_44, c_176])).
% 2.34/1.30  tff(c_12, plain, (![C_8, B_7, A_6]: (~v1_xboole_0(C_8) | ~m1_subset_1(B_7, k1_zfmisc_1(C_8)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.34/1.30  tff(c_191, plain, (![A_6]: (~v1_xboole_0(k2_struct_0('#skF_3')) | ~r2_hidden(A_6, '#skF_2'('#skF_3')))), inference(resolution, [status(thm)], [c_177, c_12])).
% 2.34/1.30  tff(c_193, plain, (~v1_xboole_0(k2_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_191])).
% 2.34/1.30  tff(c_38, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.34/1.30  tff(c_92, plain, (m1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_38])).
% 2.34/1.30  tff(c_10, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.34/1.30  tff(c_32, plain, (![A_38]: (v3_pre_topc(k2_struct_0(A_38), A_38) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.34/1.30  tff(c_6, plain, (![A_2]: (k2_subset_1(A_2)=A_2)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.34/1.30  tff(c_8, plain, (![A_3]: (m1_subset_1(k2_subset_1(A_3), k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.34/1.30  tff(c_55, plain, (![A_3]: (m1_subset_1(A_3, k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 2.34/1.30  tff(c_52, plain, (![D_50]: (v3_pre_topc(D_50, '#skF_3') | ~r2_hidden(D_50, '#skF_5') | ~m1_subset_1(D_50, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.34/1.30  tff(c_105, plain, (![D_62]: (v3_pre_topc(D_62, '#skF_3') | ~r2_hidden(D_62, '#skF_5') | ~m1_subset_1(D_62, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_52])).
% 2.34/1.30  tff(c_110, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~r2_hidden(k2_struct_0('#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_55, c_105])).
% 2.34/1.30  tff(c_123, plain, (~r2_hidden(k2_struct_0('#skF_3'), '#skF_5')), inference(splitLeft, [status(thm)], [c_110])).
% 2.34/1.30  tff(c_46, plain, (![D_50]: (r2_hidden(D_50, '#skF_5') | ~r2_hidden('#skF_4', D_50) | ~v4_pre_topc(D_50, '#skF_3') | ~v3_pre_topc(D_50, '#skF_3') | ~m1_subset_1(D_50, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.34/1.30  tff(c_195, plain, (![D_79]: (r2_hidden(D_79, '#skF_5') | ~r2_hidden('#skF_4', D_79) | ~v4_pre_topc(D_79, '#skF_3') | ~v3_pre_topc(D_79, '#skF_3') | ~m1_subset_1(D_79, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_46])).
% 2.34/1.30  tff(c_202, plain, (r2_hidden(k2_struct_0('#skF_3'), '#skF_5') | ~r2_hidden('#skF_4', k2_struct_0('#skF_3')) | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_55, c_195])).
% 2.34/1.30  tff(c_206, plain, (~r2_hidden('#skF_4', k2_struct_0('#skF_3')) | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_123, c_202])).
% 2.34/1.30  tff(c_213, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_206])).
% 2.34/1.30  tff(c_225, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_32, c_213])).
% 2.34/1.30  tff(c_229, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_225])).
% 2.34/1.30  tff(c_230, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~r2_hidden('#skF_4', k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_206])).
% 2.34/1.30  tff(c_232, plain, (~r2_hidden('#skF_4', k2_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_230])).
% 2.34/1.30  tff(c_237, plain, (v1_xboole_0(k2_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_10, c_232])).
% 2.34/1.30  tff(c_240, plain, (v1_xboole_0(k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_237])).
% 2.34/1.30  tff(c_242, plain, $false, inference(negUnitSimplification, [status(thm)], [c_193, c_240])).
% 2.34/1.30  tff(c_243, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_230])).
% 2.34/1.30  tff(c_255, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_24, c_243])).
% 2.34/1.30  tff(c_259, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_255])).
% 2.34/1.30  tff(c_326, plain, (![A_87]: (~r2_hidden(A_87, '#skF_2'('#skF_3')))), inference(splitRight, [status(thm)], [c_191])).
% 2.34/1.30  tff(c_336, plain, ('#skF_2'('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_53, c_326])).
% 2.34/1.30  tff(c_28, plain, (![A_36]: (~v1_xboole_0('#skF_2'(A_36)) | ~l1_pre_topc(A_36) | ~v2_pre_topc(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.34/1.30  tff(c_349, plain, (~v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_336, c_28])).
% 2.34/1.30  tff(c_359, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_57, c_349])).
% 2.34/1.30  tff(c_361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_359])).
% 2.34/1.30  tff(c_363, plain, (r2_hidden(k2_struct_0('#skF_3'), '#skF_5')), inference(splitRight, [status(thm)], [c_110])).
% 2.34/1.30  tff(c_14, plain, (![B_10, A_9]: (~r1_tarski(B_10, A_9) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.34/1.30  tff(c_367, plain, (~r1_tarski('#skF_5', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_363, c_14])).
% 2.34/1.30  tff(c_371, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_367])).
% 2.34/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.30  
% 2.34/1.30  Inference rules
% 2.34/1.30  ----------------------
% 2.34/1.30  #Ref     : 0
% 2.34/1.30  #Sup     : 57
% 2.34/1.30  #Fact    : 0
% 2.34/1.30  #Define  : 0
% 2.34/1.30  #Split   : 7
% 2.34/1.30  #Chain   : 0
% 2.34/1.30  #Close   : 0
% 2.34/1.30  
% 2.34/1.30  Ordering : KBO
% 2.34/1.30  
% 2.34/1.30  Simplification rules
% 2.34/1.30  ----------------------
% 2.34/1.30  #Subsume      : 5
% 2.34/1.30  #Demod        : 57
% 2.34/1.30  #Tautology    : 22
% 2.34/1.30  #SimpNegUnit  : 9
% 2.34/1.30  #BackRed      : 15
% 2.34/1.30  
% 2.34/1.30  #Partial instantiations: 0
% 2.34/1.30  #Strategies tried      : 1
% 2.34/1.30  
% 2.34/1.30  Timing (in seconds)
% 2.34/1.30  ----------------------
% 2.34/1.31  Preprocessing        : 0.31
% 2.34/1.31  Parsing              : 0.17
% 2.34/1.31  CNF conversion       : 0.02
% 2.34/1.31  Main loop            : 0.23
% 2.34/1.31  Inferencing          : 0.08
% 2.34/1.31  Reduction            : 0.07
% 2.34/1.31  Demodulation         : 0.05
% 2.34/1.31  BG Simplification    : 0.01
% 2.34/1.31  Subsumption          : 0.04
% 2.34/1.31  Abstraction          : 0.01
% 2.34/1.31  MUC search           : 0.00
% 2.34/1.31  Cooper               : 0.00
% 2.34/1.31  Total                : 0.57
% 2.34/1.31  Index Insertion      : 0.00
% 2.34/1.31  Index Deletion       : 0.00
% 2.34/1.31  Index Matching       : 0.00
% 2.34/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
