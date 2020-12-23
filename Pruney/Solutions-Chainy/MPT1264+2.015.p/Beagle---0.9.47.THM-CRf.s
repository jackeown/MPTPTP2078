%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:40 EST 2020

% Result     : Theorem 4.81s
% Output     : CNFRefutation 4.81s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 251 expanded)
%              Number of leaves         :   33 ( 102 expanded)
%              Depth                    :   14
%              Number of atoms          :  126 ( 594 expanded)
%              Number of equality atoms :   30 ( 137 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v1_tops_1(B,A)
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( v3_pre_topc(C,A)
                   => k2_pre_topc(A,C) = k2_pre_topc(A,k9_subset_1(u1_struct_0(A),C,B)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tops_1)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( v3_pre_topc(B,A)
               => k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C))) = k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tops_1)).

tff(c_38,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_20,plain,(
    ! [A_20] :
      ( l1_struct_0(A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_42,plain,(
    ! [A_36] :
      ( u1_struct_0(A_36) = k2_struct_0(A_36)
      | ~ l1_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_47,plain,(
    ! [A_37] :
      ( u1_struct_0(A_37) = k2_struct_0(A_37)
      | ~ l1_pre_topc(A_37) ) ),
    inference(resolution,[status(thm)],[c_20,c_42])).

tff(c_51,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_47])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_53,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_36])).

tff(c_98,plain,(
    ! [A_54,B_55,C_56] :
      ( k9_subset_1(A_54,B_55,C_56) = k3_xboole_0(B_55,C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_104,plain,(
    ! [B_55] : k9_subset_1(k2_struct_0('#skF_2'),B_55,'#skF_3') = k3_xboole_0(B_55,'#skF_3') ),
    inference(resolution,[status(thm)],[c_53,c_98])).

tff(c_28,plain,(
    k2_pre_topc('#skF_2',k9_subset_1(u1_struct_0('#skF_2'),'#skF_4','#skF_3')) != k2_pre_topc('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_52,plain,(
    k2_pre_topc('#skF_2',k9_subset_1(k2_struct_0('#skF_2'),'#skF_4','#skF_3')) != k2_pre_topc('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_28])).

tff(c_114,plain,(
    k2_pre_topc('#skF_2',k3_xboole_0('#skF_4','#skF_3')) != k2_pre_topc('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_52])).

tff(c_30,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_32])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_94,plain,(
    ! [C_51,A_52,B_53] :
      ( r2_hidden(C_51,A_52)
      | ~ r2_hidden(C_51,B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_145,plain,(
    ! [A_64,B_65,A_66] :
      ( r2_hidden('#skF_1'(A_64,B_65),A_66)
      | ~ m1_subset_1(A_64,k1_zfmisc_1(A_66))
      | r1_tarski(A_64,B_65) ) ),
    inference(resolution,[status(thm)],[c_6,c_94])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_161,plain,(
    ! [A_68,A_69] :
      ( ~ m1_subset_1(A_68,k1_zfmisc_1(A_69))
      | r1_tarski(A_68,A_69) ) ),
    inference(resolution,[status(thm)],[c_145,c_4])).

tff(c_176,plain,(
    r1_tarski('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_161])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_181,plain,(
    k3_xboole_0('#skF_4',k2_struct_0('#skF_2')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_176,c_8])).

tff(c_34,plain,(
    v1_tops_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_194,plain,(
    ! [A_70,B_71] :
      ( k2_pre_topc(A_70,B_71) = k2_struct_0(A_70)
      | ~ v1_tops_1(B_71,A_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_200,plain,(
    ! [B_71] :
      ( k2_pre_topc('#skF_2',B_71) = k2_struct_0('#skF_2')
      | ~ v1_tops_1(B_71,'#skF_2')
      | ~ m1_subset_1(B_71,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_194])).

tff(c_219,plain,(
    ! [B_75] :
      ( k2_pre_topc('#skF_2',B_75) = k2_struct_0('#skF_2')
      | ~ v1_tops_1(B_75,'#skF_2')
      | ~ m1_subset_1(B_75,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_200])).

tff(c_228,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = k2_struct_0('#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_53,c_219])).

tff(c_233,plain,(
    k2_pre_topc('#skF_2','#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_228])).

tff(c_124,plain,(
    ! [A_59,B_60] :
      ( m1_subset_1(k2_pre_topc(A_59,B_60),k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_129,plain,(
    ! [B_60] :
      ( m1_subset_1(k2_pre_topc('#skF_2',B_60),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_124])).

tff(c_132,plain,(
    ! [B_60] :
      ( m1_subset_1(k2_pre_topc('#skF_2',B_60),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_51,c_129])).

tff(c_244,plain,
    ( m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_132])).

tff(c_255,plain,(
    m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_244])).

tff(c_12,plain,(
    ! [A_12,B_13,C_14] :
      ( k9_subset_1(A_12,B_13,C_14) = k3_xboole_0(B_13,C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_270,plain,(
    ! [B_13] : k9_subset_1(k2_struct_0('#skF_2'),B_13,k2_struct_0('#skF_2')) = k3_xboole_0(B_13,k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_255,c_12])).

tff(c_40,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_390,plain,(
    ! [A_88,B_89,C_90] :
      ( k2_pre_topc(A_88,k9_subset_1(u1_struct_0(A_88),B_89,k2_pre_topc(A_88,C_90))) = k2_pre_topc(A_88,k9_subset_1(u1_struct_0(A_88),B_89,C_90))
      | ~ v3_pre_topc(B_89,A_88)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_422,plain,(
    ! [B_89,C_90] :
      ( k2_pre_topc('#skF_2',k9_subset_1(k2_struct_0('#skF_2'),B_89,k2_pre_topc('#skF_2',C_90))) = k2_pre_topc('#skF_2',k9_subset_1(u1_struct_0('#skF_2'),B_89,C_90))
      | ~ v3_pre_topc(B_89,'#skF_2')
      | ~ m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_390])).

tff(c_500,plain,(
    ! [B_95,C_96] :
      ( k2_pre_topc('#skF_2',k9_subset_1(k2_struct_0('#skF_2'),B_95,k2_pre_topc('#skF_2',C_96))) = k2_pre_topc('#skF_2',k9_subset_1(k2_struct_0('#skF_2'),B_95,C_96))
      | ~ v3_pre_topc(B_95,'#skF_2')
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_51,c_51,c_51,c_422])).

tff(c_534,plain,(
    ! [B_95] :
      ( k2_pre_topc('#skF_2',k9_subset_1(k2_struct_0('#skF_2'),B_95,k2_struct_0('#skF_2'))) = k2_pre_topc('#skF_2',k9_subset_1(k2_struct_0('#skF_2'),B_95,'#skF_3'))
      | ~ v3_pre_topc(B_95,'#skF_2')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_500])).

tff(c_1537,plain,(
    ! [B_235] :
      ( k2_pre_topc('#skF_2',k3_xboole_0(B_235,k2_struct_0('#skF_2'))) = k2_pre_topc('#skF_2',k3_xboole_0(B_235,'#skF_3'))
      | ~ v3_pre_topc(B_235,'#skF_2')
      | ~ m1_subset_1(B_235,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_270,c_104,c_534])).

tff(c_1546,plain,
    ( k2_pre_topc('#skF_2',k3_xboole_0('#skF_4',k2_struct_0('#skF_2'))) = k2_pre_topc('#skF_2',k3_xboole_0('#skF_4','#skF_3'))
    | ~ v3_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_1537])).

tff(c_1555,plain,(
    k2_pre_topc('#skF_2',k3_xboole_0('#skF_4','#skF_3')) = k2_pre_topc('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_181,c_1546])).

tff(c_1557,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_1555])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:28:35 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.81/1.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.81/1.87  
% 4.81/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.81/1.87  %$ v3_pre_topc > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.81/1.87  
% 4.81/1.87  %Foreground sorts:
% 4.81/1.87  
% 4.81/1.87  
% 4.81/1.87  %Background operators:
% 4.81/1.87  
% 4.81/1.87  
% 4.81/1.87  %Foreground operators:
% 4.81/1.87  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.81/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.81/1.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.81/1.87  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.81/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.81/1.87  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.81/1.87  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 4.81/1.87  tff('#skF_2', type, '#skF_2': $i).
% 4.81/1.87  tff('#skF_3', type, '#skF_3': $i).
% 4.81/1.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.81/1.87  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.81/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.81/1.87  tff('#skF_4', type, '#skF_4': $i).
% 4.81/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.81/1.87  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.81/1.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.81/1.87  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.81/1.87  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.81/1.87  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.81/1.87  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.81/1.87  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.81/1.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.81/1.87  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.81/1.87  
% 4.81/1.89  tff(f_103, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(C, A) => (k2_pre_topc(A, C) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), C, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_tops_1)).
% 4.81/1.89  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.81/1.89  tff(f_53, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.81/1.89  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.81/1.89  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.81/1.89  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 4.81/1.89  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.81/1.89  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 4.81/1.89  tff(f_59, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 4.81/1.89  tff(f_86, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => (k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C))) = k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tops_1)).
% 4.81/1.89  tff(c_38, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.81/1.89  tff(c_20, plain, (![A_20]: (l1_struct_0(A_20) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.81/1.89  tff(c_42, plain, (![A_36]: (u1_struct_0(A_36)=k2_struct_0(A_36) | ~l1_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.81/1.89  tff(c_47, plain, (![A_37]: (u1_struct_0(A_37)=k2_struct_0(A_37) | ~l1_pre_topc(A_37))), inference(resolution, [status(thm)], [c_20, c_42])).
% 4.81/1.89  tff(c_51, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_47])).
% 4.81/1.89  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.81/1.89  tff(c_53, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_36])).
% 4.81/1.89  tff(c_98, plain, (![A_54, B_55, C_56]: (k9_subset_1(A_54, B_55, C_56)=k3_xboole_0(B_55, C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.81/1.89  tff(c_104, plain, (![B_55]: (k9_subset_1(k2_struct_0('#skF_2'), B_55, '#skF_3')=k3_xboole_0(B_55, '#skF_3'))), inference(resolution, [status(thm)], [c_53, c_98])).
% 4.81/1.89  tff(c_28, plain, (k2_pre_topc('#skF_2', k9_subset_1(u1_struct_0('#skF_2'), '#skF_4', '#skF_3'))!=k2_pre_topc('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.81/1.89  tff(c_52, plain, (k2_pre_topc('#skF_2', k9_subset_1(k2_struct_0('#skF_2'), '#skF_4', '#skF_3'))!=k2_pre_topc('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_51, c_28])).
% 4.81/1.89  tff(c_114, plain, (k2_pre_topc('#skF_2', k3_xboole_0('#skF_4', '#skF_3'))!=k2_pre_topc('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_52])).
% 4.81/1.89  tff(c_30, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.81/1.89  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.81/1.89  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_32])).
% 4.81/1.89  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.81/1.89  tff(c_94, plain, (![C_51, A_52, B_53]: (r2_hidden(C_51, A_52) | ~r2_hidden(C_51, B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.81/1.89  tff(c_145, plain, (![A_64, B_65, A_66]: (r2_hidden('#skF_1'(A_64, B_65), A_66) | ~m1_subset_1(A_64, k1_zfmisc_1(A_66)) | r1_tarski(A_64, B_65))), inference(resolution, [status(thm)], [c_6, c_94])).
% 4.81/1.89  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.81/1.89  tff(c_161, plain, (![A_68, A_69]: (~m1_subset_1(A_68, k1_zfmisc_1(A_69)) | r1_tarski(A_68, A_69))), inference(resolution, [status(thm)], [c_145, c_4])).
% 4.81/1.89  tff(c_176, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_54, c_161])).
% 4.81/1.89  tff(c_8, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.81/1.89  tff(c_181, plain, (k3_xboole_0('#skF_4', k2_struct_0('#skF_2'))='#skF_4'), inference(resolution, [status(thm)], [c_176, c_8])).
% 4.81/1.89  tff(c_34, plain, (v1_tops_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.81/1.89  tff(c_194, plain, (![A_70, B_71]: (k2_pre_topc(A_70, B_71)=k2_struct_0(A_70) | ~v1_tops_1(B_71, A_70) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.81/1.89  tff(c_200, plain, (![B_71]: (k2_pre_topc('#skF_2', B_71)=k2_struct_0('#skF_2') | ~v1_tops_1(B_71, '#skF_2') | ~m1_subset_1(B_71, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_51, c_194])).
% 4.81/1.89  tff(c_219, plain, (![B_75]: (k2_pre_topc('#skF_2', B_75)=k2_struct_0('#skF_2') | ~v1_tops_1(B_75, '#skF_2') | ~m1_subset_1(B_75, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_200])).
% 4.81/1.89  tff(c_228, plain, (k2_pre_topc('#skF_2', '#skF_3')=k2_struct_0('#skF_2') | ~v1_tops_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_53, c_219])).
% 4.81/1.89  tff(c_233, plain, (k2_pre_topc('#skF_2', '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_228])).
% 4.81/1.89  tff(c_124, plain, (![A_59, B_60]: (m1_subset_1(k2_pre_topc(A_59, B_60), k1_zfmisc_1(u1_struct_0(A_59))) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.81/1.89  tff(c_129, plain, (![B_60]: (m1_subset_1(k2_pre_topc('#skF_2', B_60), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_51, c_124])).
% 4.81/1.89  tff(c_132, plain, (![B_60]: (m1_subset_1(k2_pre_topc('#skF_2', B_60), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_60, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_51, c_129])).
% 4.81/1.89  tff(c_244, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_233, c_132])).
% 4.81/1.89  tff(c_255, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_244])).
% 4.81/1.89  tff(c_12, plain, (![A_12, B_13, C_14]: (k9_subset_1(A_12, B_13, C_14)=k3_xboole_0(B_13, C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.81/1.89  tff(c_270, plain, (![B_13]: (k9_subset_1(k2_struct_0('#skF_2'), B_13, k2_struct_0('#skF_2'))=k3_xboole_0(B_13, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_255, c_12])).
% 4.81/1.89  tff(c_40, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.81/1.89  tff(c_390, plain, (![A_88, B_89, C_90]: (k2_pre_topc(A_88, k9_subset_1(u1_struct_0(A_88), B_89, k2_pre_topc(A_88, C_90)))=k2_pre_topc(A_88, k9_subset_1(u1_struct_0(A_88), B_89, C_90)) | ~v3_pre_topc(B_89, A_88) | ~m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0(A_88))) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.81/1.89  tff(c_422, plain, (![B_89, C_90]: (k2_pre_topc('#skF_2', k9_subset_1(k2_struct_0('#skF_2'), B_89, k2_pre_topc('#skF_2', C_90)))=k2_pre_topc('#skF_2', k9_subset_1(u1_struct_0('#skF_2'), B_89, C_90)) | ~v3_pre_topc(B_89, '#skF_2') | ~m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_51, c_390])).
% 4.81/1.89  tff(c_500, plain, (![B_95, C_96]: (k2_pre_topc('#skF_2', k9_subset_1(k2_struct_0('#skF_2'), B_95, k2_pre_topc('#skF_2', C_96)))=k2_pre_topc('#skF_2', k9_subset_1(k2_struct_0('#skF_2'), B_95, C_96)) | ~v3_pre_topc(B_95, '#skF_2') | ~m1_subset_1(C_96, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_95, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_51, c_51, c_51, c_422])).
% 4.81/1.89  tff(c_534, plain, (![B_95]: (k2_pre_topc('#skF_2', k9_subset_1(k2_struct_0('#skF_2'), B_95, k2_struct_0('#skF_2')))=k2_pre_topc('#skF_2', k9_subset_1(k2_struct_0('#skF_2'), B_95, '#skF_3')) | ~v3_pre_topc(B_95, '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(B_95, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_233, c_500])).
% 4.81/1.89  tff(c_1537, plain, (![B_235]: (k2_pre_topc('#skF_2', k3_xboole_0(B_235, k2_struct_0('#skF_2')))=k2_pre_topc('#skF_2', k3_xboole_0(B_235, '#skF_3')) | ~v3_pre_topc(B_235, '#skF_2') | ~m1_subset_1(B_235, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_270, c_104, c_534])).
% 4.81/1.89  tff(c_1546, plain, (k2_pre_topc('#skF_2', k3_xboole_0('#skF_4', k2_struct_0('#skF_2')))=k2_pre_topc('#skF_2', k3_xboole_0('#skF_4', '#skF_3')) | ~v3_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_54, c_1537])).
% 4.81/1.89  tff(c_1555, plain, (k2_pre_topc('#skF_2', k3_xboole_0('#skF_4', '#skF_3'))=k2_pre_topc('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_181, c_1546])).
% 4.81/1.89  tff(c_1557, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_1555])).
% 4.81/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.81/1.89  
% 4.81/1.89  Inference rules
% 4.81/1.89  ----------------------
% 4.81/1.89  #Ref     : 0
% 4.81/1.89  #Sup     : 384
% 4.81/1.89  #Fact    : 0
% 4.81/1.89  #Define  : 0
% 4.81/1.89  #Split   : 9
% 4.81/1.89  #Chain   : 0
% 4.81/1.89  #Close   : 0
% 4.81/1.89  
% 4.81/1.89  Ordering : KBO
% 4.81/1.89  
% 4.81/1.89  Simplification rules
% 4.81/1.89  ----------------------
% 4.81/1.89  #Subsume      : 126
% 4.81/1.89  #Demod        : 268
% 4.81/1.89  #Tautology    : 78
% 4.81/1.89  #SimpNegUnit  : 9
% 4.81/1.89  #BackRed      : 4
% 4.81/1.89  
% 4.81/1.89  #Partial instantiations: 0
% 4.81/1.89  #Strategies tried      : 1
% 4.81/1.89  
% 4.81/1.89  Timing (in seconds)
% 4.81/1.89  ----------------------
% 4.81/1.89  Preprocessing        : 0.33
% 4.81/1.89  Parsing              : 0.18
% 4.81/1.89  CNF conversion       : 0.02
% 4.81/1.89  Main loop            : 0.79
% 4.81/1.89  Inferencing          : 0.25
% 4.81/1.89  Reduction            : 0.25
% 4.81/1.89  Demodulation         : 0.18
% 4.81/1.89  BG Simplification    : 0.03
% 4.81/1.89  Subsumption          : 0.21
% 4.81/1.89  Abstraction          : 0.04
% 4.81/1.89  MUC search           : 0.00
% 4.81/1.89  Cooper               : 0.00
% 4.81/1.89  Total                : 1.16
% 4.81/1.89  Index Insertion      : 0.00
% 4.81/1.89  Index Deletion       : 0.00
% 4.81/1.89  Index Matching       : 0.00
% 4.81/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
