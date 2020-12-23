%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:00 EST 2020

% Result     : Theorem 14.78s
% Output     : CNFRefutation 14.78s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 702 expanded)
%              Number of leaves         :   39 ( 262 expanded)
%              Depth                    :   16
%              Number of atoms          :  148 (2137 expanded)
%              Number of equality atoms :   19 ( 229 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_142,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_pre_topc(C,A)
               => ( v3_pre_topc(B,A)
                 => ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                     => ( D = B
                       => v3_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( ( v1_pre_topc(C)
                & m1_pre_topc(C,A) )
             => ( C = k1_pre_topc(A,B)
              <=> k2_struct_0(C) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_pre_topc)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(B,A)
          <=> ( r1_tarski(k2_struct_0(B),k2_struct_0(A))
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
                 => ( r2_hidden(C,u1_pre_topc(B))
                  <=> ? [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                        & r2_hidden(D,u1_pre_topc(A))
                        & C = k9_subset_1(u1_struct_0(B),D,k2_struct_0(B)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_124,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => ( v3_pre_topc(C,B)
              <=> ? [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                    & v3_pre_topc(D,A)
                    & k9_subset_1(u1_struct_0(B),D,k2_struct_0(B)) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tops_2)).

tff(c_64,plain,(
    ~ v3_pre_topc('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_76,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_72,plain,(
    m1_pre_topc('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_95,plain,(
    ! [B_107,A_108] :
      ( l1_pre_topc(B_107)
      | ~ m1_pre_topc(B_107,A_108)
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_98,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_95])).

tff(c_101,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_98])).

tff(c_50,plain,(
    ! [A_60] :
      ( l1_struct_0(A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_68,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_177,plain,(
    ! [A_125,B_126] :
      ( m1_pre_topc(k1_pre_topc(A_125,B_126),A_125)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_pre_topc(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_183,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_7','#skF_8'),'#skF_7')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_177])).

tff(c_193,plain,(
    m1_pre_topc(k1_pre_topc('#skF_7','#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_183])).

tff(c_52,plain,(
    ! [B_63,A_61] :
      ( l1_pre_topc(B_63)
      | ~ m1_pre_topc(B_63,A_61)
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_208,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_7','#skF_8'))
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_193,c_52])).

tff(c_211,plain,(
    l1_pre_topc(k1_pre_topc('#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_208])).

tff(c_153,plain,(
    ! [A_121,B_122] :
      ( v1_pre_topc(k1_pre_topc(A_121,B_122))
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ l1_pre_topc(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_162,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_7','#skF_8'))
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_153])).

tff(c_173,plain,(
    v1_pre_topc(k1_pre_topc('#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_162])).

tff(c_870,plain,(
    ! [A_218,B_219] :
      ( k2_struct_0(k1_pre_topc(A_218,B_219)) = B_219
      | ~ m1_pre_topc(k1_pre_topc(A_218,B_219),A_218)
      | ~ v1_pre_topc(k1_pre_topc(A_218,B_219))
      | ~ m1_subset_1(B_219,k1_zfmisc_1(u1_struct_0(A_218)))
      | ~ l1_pre_topc(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_894,plain,
    ( k2_struct_0(k1_pre_topc('#skF_7','#skF_8')) = '#skF_8'
    | ~ v1_pre_topc(k1_pre_topc('#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7')))
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_193,c_870])).

tff(c_917,plain,(
    k2_struct_0(k1_pre_topc('#skF_7','#skF_8')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_68,c_173,c_894])).

tff(c_195,plain,(
    ! [B_127,A_128] :
      ( r1_tarski(k2_struct_0(B_127),k2_struct_0(A_128))
      | ~ m1_pre_topc(B_127,A_128)
      | ~ l1_pre_topc(B_127)
      | ~ l1_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_199,plain,(
    ! [B_127,A_128] :
      ( k3_xboole_0(k2_struct_0(B_127),k2_struct_0(A_128)) = k2_struct_0(B_127)
      | ~ m1_pre_topc(B_127,A_128)
      | ~ l1_pre_topc(B_127)
      | ~ l1_pre_topc(A_128) ) ),
    inference(resolution,[status(thm)],[c_195,c_2])).

tff(c_927,plain,(
    ! [A_128] :
      ( k3_xboole_0('#skF_8',k2_struct_0(A_128)) = k2_struct_0(k1_pre_topc('#skF_7','#skF_8'))
      | ~ m1_pre_topc(k1_pre_topc('#skF_7','#skF_8'),A_128)
      | ~ l1_pre_topc(k1_pre_topc('#skF_7','#skF_8'))
      | ~ l1_pre_topc(A_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_917,c_199])).

tff(c_1560,plain,(
    ! [A_239] :
      ( k3_xboole_0('#skF_8',k2_struct_0(A_239)) = '#skF_8'
      | ~ m1_pre_topc(k1_pre_topc('#skF_7','#skF_8'),A_239)
      | ~ l1_pre_topc(A_239) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_917,c_927])).

tff(c_1571,plain,
    ( k3_xboole_0('#skF_8',k2_struct_0('#skF_7')) = '#skF_8'
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_193,c_1560])).

tff(c_1580,plain,(
    k3_xboole_0('#skF_8',k2_struct_0('#skF_7')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_1571])).

tff(c_48,plain,(
    ! [A_59] :
      ( m1_subset_1(k2_struct_0(A_59),k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_113,plain,(
    ! [A_114,B_115,C_116] :
      ( k9_subset_1(A_114,B_115,C_116) = k3_xboole_0(B_115,C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(A_114)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_122,plain,(
    ! [A_59,B_115] :
      ( k9_subset_1(u1_struct_0(A_59),B_115,k2_struct_0(A_59)) = k3_xboole_0(B_115,k2_struct_0(A_59))
      | ~ l1_struct_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_48,c_113])).

tff(c_66,plain,(
    '#skF_6' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_70,plain,(
    v3_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_77,plain,(
    v3_pre_topc('#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70])).

tff(c_74,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_78,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_74])).

tff(c_2365,plain,(
    ! [B_269,D_270,A_271] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_269),D_270,k2_struct_0(B_269)),B_269)
      | ~ v3_pre_topc(D_270,A_271)
      | ~ m1_subset_1(D_270,k1_zfmisc_1(u1_struct_0(A_271)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_269),D_270,k2_struct_0(B_269)),k1_zfmisc_1(u1_struct_0(B_269)))
      | ~ m1_pre_topc(B_269,A_271)
      | ~ l1_pre_topc(A_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2401,plain,(
    ! [B_269] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_269),'#skF_8',k2_struct_0(B_269)),B_269)
      | ~ v3_pre_topc('#skF_8','#skF_5')
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_269),'#skF_8',k2_struct_0(B_269)),k1_zfmisc_1(u1_struct_0(B_269)))
      | ~ m1_pre_topc(B_269,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_78,c_2365])).

tff(c_3361,plain,(
    ! [B_315] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_315),'#skF_8',k2_struct_0(B_315)),B_315)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_315),'#skF_8',k2_struct_0(B_315)),k1_zfmisc_1(u1_struct_0(B_315)))
      | ~ m1_pre_topc(B_315,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_77,c_2401])).

tff(c_24516,plain,(
    ! [A_854] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(A_854),'#skF_8',k2_struct_0(A_854)),A_854)
      | ~ m1_subset_1(k3_xboole_0('#skF_8',k2_struct_0(A_854)),k1_zfmisc_1(u1_struct_0(A_854)))
      | ~ m1_pre_topc(A_854,'#skF_5')
      | ~ l1_struct_0(A_854) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_3361])).

tff(c_24538,plain,
    ( v3_pre_topc(k9_subset_1(u1_struct_0('#skF_7'),'#skF_8',k2_struct_0('#skF_7')),'#skF_7')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7')))
    | ~ m1_pre_topc('#skF_7','#skF_5')
    | ~ l1_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1580,c_24516])).

tff(c_24562,plain,
    ( v3_pre_topc(k9_subset_1(u1_struct_0('#skF_7'),'#skF_8',k2_struct_0('#skF_7')),'#skF_7')
    | ~ l1_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_24538])).

tff(c_24572,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_24562])).

tff(c_24575,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_50,c_24572])).

tff(c_24579,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_24575])).

tff(c_24581,plain,(
    l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_24562])).

tff(c_24580,plain,(
    v3_pre_topc(k9_subset_1(u1_struct_0('#skF_7'),'#skF_8',k2_struct_0('#skF_7')),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_24562])).

tff(c_24591,plain,
    ( v3_pre_topc(k3_xboole_0('#skF_8',k2_struct_0('#skF_7')),'#skF_7')
    | ~ l1_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_24580])).

tff(c_24599,plain,(
    v3_pre_topc('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24581,c_1580,c_24591])).

tff(c_24601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_24599])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:29:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.78/6.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.78/6.53  
% 14.78/6.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.78/6.53  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2
% 14.78/6.53  
% 14.78/6.53  %Foreground sorts:
% 14.78/6.53  
% 14.78/6.53  
% 14.78/6.53  %Background operators:
% 14.78/6.53  
% 14.78/6.53  
% 14.78/6.53  %Foreground operators:
% 14.78/6.53  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 14.78/6.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 14.78/6.53  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 14.78/6.53  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 14.78/6.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.78/6.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.78/6.53  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 14.78/6.53  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 14.78/6.53  tff('#skF_7', type, '#skF_7': $i).
% 14.78/6.53  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 14.78/6.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.78/6.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.78/6.53  tff('#skF_5', type, '#skF_5': $i).
% 14.78/6.53  tff('#skF_6', type, '#skF_6': $i).
% 14.78/6.53  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 14.78/6.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.78/6.53  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 14.78/6.53  tff('#skF_8', type, '#skF_8': $i).
% 14.78/6.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.78/6.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.78/6.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 14.78/6.53  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 14.78/6.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.78/6.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 14.78/6.53  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 14.78/6.53  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 14.78/6.53  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 14.78/6.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.78/6.53  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 14.78/6.53  
% 14.78/6.54  tff(f_142, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tops_2)).
% 14.78/6.54  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 14.78/6.54  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 14.78/6.54  tff(f_82, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 14.78/6.54  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((v1_pre_topc(C) & m1_pre_topc(C, A)) => ((C = k1_pre_topc(A, B)) <=> (k2_struct_0(C) = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_pre_topc)).
% 14.78/6.54  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(B, A) <=> (r1_tarski(k2_struct_0(B), k2_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (r2_hidden(C, u1_pre_topc(B)) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(D, u1_pre_topc(A))) & (C = k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_pre_topc)).
% 14.78/6.54  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 14.78/6.54  tff(f_86, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 14.78/6.54  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 14.78/6.54  tff(f_124, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (v3_pre_topc(C, B) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & (k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)) = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_tops_2)).
% 14.78/6.54  tff(c_64, plain, (~v3_pre_topc('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_142])).
% 14.78/6.54  tff(c_76, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_142])).
% 14.78/6.54  tff(c_72, plain, (m1_pre_topc('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_142])).
% 14.78/6.54  tff(c_95, plain, (![B_107, A_108]: (l1_pre_topc(B_107) | ~m1_pre_topc(B_107, A_108) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_97])).
% 14.78/6.54  tff(c_98, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_72, c_95])).
% 14.78/6.54  tff(c_101, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_98])).
% 14.78/6.54  tff(c_50, plain, (![A_60]: (l1_struct_0(A_60) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_90])).
% 14.78/6.54  tff(c_68, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_7')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 14.78/6.54  tff(c_177, plain, (![A_125, B_126]: (m1_pre_topc(k1_pre_topc(A_125, B_126), A_125) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_125))) | ~l1_pre_topc(A_125))), inference(cnfTransformation, [status(thm)], [f_82])).
% 14.78/6.54  tff(c_183, plain, (m1_pre_topc(k1_pre_topc('#skF_7', '#skF_8'), '#skF_7') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_68, c_177])).
% 14.78/6.54  tff(c_193, plain, (m1_pre_topc(k1_pre_topc('#skF_7', '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_183])).
% 14.78/6.54  tff(c_52, plain, (![B_63, A_61]: (l1_pre_topc(B_63) | ~m1_pre_topc(B_63, A_61) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_97])).
% 14.78/6.54  tff(c_208, plain, (l1_pre_topc(k1_pre_topc('#skF_7', '#skF_8')) | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_193, c_52])).
% 14.78/6.54  tff(c_211, plain, (l1_pre_topc(k1_pre_topc('#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_208])).
% 14.78/6.54  tff(c_153, plain, (![A_121, B_122]: (v1_pre_topc(k1_pre_topc(A_121, B_122)) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(A_121))) | ~l1_pre_topc(A_121))), inference(cnfTransformation, [status(thm)], [f_82])).
% 14.78/6.54  tff(c_162, plain, (v1_pre_topc(k1_pre_topc('#skF_7', '#skF_8')) | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_68, c_153])).
% 14.78/6.54  tff(c_173, plain, (v1_pre_topc(k1_pre_topc('#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_162])).
% 14.78/6.54  tff(c_870, plain, (![A_218, B_219]: (k2_struct_0(k1_pre_topc(A_218, B_219))=B_219 | ~m1_pre_topc(k1_pre_topc(A_218, B_219), A_218) | ~v1_pre_topc(k1_pre_topc(A_218, B_219)) | ~m1_subset_1(B_219, k1_zfmisc_1(u1_struct_0(A_218))) | ~l1_pre_topc(A_218))), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.78/6.54  tff(c_894, plain, (k2_struct_0(k1_pre_topc('#skF_7', '#skF_8'))='#skF_8' | ~v1_pre_topc(k1_pre_topc('#skF_7', '#skF_8')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_193, c_870])).
% 14.78/6.54  tff(c_917, plain, (k2_struct_0(k1_pre_topc('#skF_7', '#skF_8'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_101, c_68, c_173, c_894])).
% 14.78/6.54  tff(c_195, plain, (![B_127, A_128]: (r1_tarski(k2_struct_0(B_127), k2_struct_0(A_128)) | ~m1_pre_topc(B_127, A_128) | ~l1_pre_topc(B_127) | ~l1_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_74])).
% 14.78/6.54  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.78/6.54  tff(c_199, plain, (![B_127, A_128]: (k3_xboole_0(k2_struct_0(B_127), k2_struct_0(A_128))=k2_struct_0(B_127) | ~m1_pre_topc(B_127, A_128) | ~l1_pre_topc(B_127) | ~l1_pre_topc(A_128))), inference(resolution, [status(thm)], [c_195, c_2])).
% 14.78/6.54  tff(c_927, plain, (![A_128]: (k3_xboole_0('#skF_8', k2_struct_0(A_128))=k2_struct_0(k1_pre_topc('#skF_7', '#skF_8')) | ~m1_pre_topc(k1_pre_topc('#skF_7', '#skF_8'), A_128) | ~l1_pre_topc(k1_pre_topc('#skF_7', '#skF_8')) | ~l1_pre_topc(A_128))), inference(superposition, [status(thm), theory('equality')], [c_917, c_199])).
% 14.78/6.54  tff(c_1560, plain, (![A_239]: (k3_xboole_0('#skF_8', k2_struct_0(A_239))='#skF_8' | ~m1_pre_topc(k1_pre_topc('#skF_7', '#skF_8'), A_239) | ~l1_pre_topc(A_239))), inference(demodulation, [status(thm), theory('equality')], [c_211, c_917, c_927])).
% 14.78/6.54  tff(c_1571, plain, (k3_xboole_0('#skF_8', k2_struct_0('#skF_7'))='#skF_8' | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_193, c_1560])).
% 14.78/6.54  tff(c_1580, plain, (k3_xboole_0('#skF_8', k2_struct_0('#skF_7'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_101, c_1571])).
% 14.78/6.54  tff(c_48, plain, (![A_59]: (m1_subset_1(k2_struct_0(A_59), k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_86])).
% 14.78/6.54  tff(c_113, plain, (![A_114, B_115, C_116]: (k9_subset_1(A_114, B_115, C_116)=k3_xboole_0(B_115, C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(A_114)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.78/6.54  tff(c_122, plain, (![A_59, B_115]: (k9_subset_1(u1_struct_0(A_59), B_115, k2_struct_0(A_59))=k3_xboole_0(B_115, k2_struct_0(A_59)) | ~l1_struct_0(A_59))), inference(resolution, [status(thm)], [c_48, c_113])).
% 14.78/6.54  tff(c_66, plain, ('#skF_6'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_142])).
% 14.78/6.54  tff(c_70, plain, (v3_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_142])).
% 14.78/6.54  tff(c_77, plain, (v3_pre_topc('#skF_8', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70])).
% 14.78/6.54  tff(c_74, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 14.78/6.54  tff(c_78, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_74])).
% 14.78/6.54  tff(c_2365, plain, (![B_269, D_270, A_271]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_269), D_270, k2_struct_0(B_269)), B_269) | ~v3_pre_topc(D_270, A_271) | ~m1_subset_1(D_270, k1_zfmisc_1(u1_struct_0(A_271))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_269), D_270, k2_struct_0(B_269)), k1_zfmisc_1(u1_struct_0(B_269))) | ~m1_pre_topc(B_269, A_271) | ~l1_pre_topc(A_271))), inference(cnfTransformation, [status(thm)], [f_124])).
% 14.78/6.54  tff(c_2401, plain, (![B_269]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_269), '#skF_8', k2_struct_0(B_269)), B_269) | ~v3_pre_topc('#skF_8', '#skF_5') | ~m1_subset_1(k9_subset_1(u1_struct_0(B_269), '#skF_8', k2_struct_0(B_269)), k1_zfmisc_1(u1_struct_0(B_269))) | ~m1_pre_topc(B_269, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_78, c_2365])).
% 14.78/6.54  tff(c_3361, plain, (![B_315]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_315), '#skF_8', k2_struct_0(B_315)), B_315) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_315), '#skF_8', k2_struct_0(B_315)), k1_zfmisc_1(u1_struct_0(B_315))) | ~m1_pre_topc(B_315, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_77, c_2401])).
% 14.78/6.54  tff(c_24516, plain, (![A_854]: (v3_pre_topc(k9_subset_1(u1_struct_0(A_854), '#skF_8', k2_struct_0(A_854)), A_854) | ~m1_subset_1(k3_xboole_0('#skF_8', k2_struct_0(A_854)), k1_zfmisc_1(u1_struct_0(A_854))) | ~m1_pre_topc(A_854, '#skF_5') | ~l1_struct_0(A_854))), inference(superposition, [status(thm), theory('equality')], [c_122, c_3361])).
% 14.78/6.54  tff(c_24538, plain, (v3_pre_topc(k9_subset_1(u1_struct_0('#skF_7'), '#skF_8', k2_struct_0('#skF_7')), '#skF_7') | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~m1_pre_topc('#skF_7', '#skF_5') | ~l1_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1580, c_24516])).
% 14.78/6.54  tff(c_24562, plain, (v3_pre_topc(k9_subset_1(u1_struct_0('#skF_7'), '#skF_8', k2_struct_0('#skF_7')), '#skF_7') | ~l1_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_24538])).
% 14.78/6.54  tff(c_24572, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_24562])).
% 14.78/6.54  tff(c_24575, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_50, c_24572])).
% 14.78/6.54  tff(c_24579, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_24575])).
% 14.78/6.54  tff(c_24581, plain, (l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_24562])).
% 14.78/6.54  tff(c_24580, plain, (v3_pre_topc(k9_subset_1(u1_struct_0('#skF_7'), '#skF_8', k2_struct_0('#skF_7')), '#skF_7')), inference(splitRight, [status(thm)], [c_24562])).
% 14.78/6.54  tff(c_24591, plain, (v3_pre_topc(k3_xboole_0('#skF_8', k2_struct_0('#skF_7')), '#skF_7') | ~l1_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_122, c_24580])).
% 14.78/6.54  tff(c_24599, plain, (v3_pre_topc('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_24581, c_1580, c_24591])).
% 14.78/6.54  tff(c_24601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_24599])).
% 14.78/6.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.78/6.54  
% 14.78/6.54  Inference rules
% 14.78/6.54  ----------------------
% 14.78/6.54  #Ref     : 0
% 14.78/6.54  #Sup     : 4994
% 14.78/6.54  #Fact    : 0
% 14.78/6.54  #Define  : 0
% 14.78/6.54  #Split   : 54
% 14.78/6.54  #Chain   : 0
% 14.78/6.54  #Close   : 0
% 14.78/6.54  
% 14.78/6.54  Ordering : KBO
% 14.78/6.54  
% 14.78/6.54  Simplification rules
% 14.78/6.54  ----------------------
% 14.78/6.54  #Subsume      : 1165
% 14.78/6.54  #Demod        : 4915
% 14.78/6.54  #Tautology    : 1001
% 14.78/6.54  #SimpNegUnit  : 41
% 14.78/6.54  #BackRed      : 0
% 14.78/6.54  
% 14.78/6.54  #Partial instantiations: 0
% 14.78/6.54  #Strategies tried      : 1
% 14.78/6.54  
% 14.78/6.54  Timing (in seconds)
% 14.78/6.54  ----------------------
% 14.78/6.54  Preprocessing        : 0.35
% 14.78/6.54  Parsing              : 0.18
% 14.78/6.54  CNF conversion       : 0.03
% 14.78/6.54  Main loop            : 5.44
% 14.78/6.54  Inferencing          : 1.22
% 14.78/6.54  Reduction            : 2.07
% 14.78/6.54  Demodulation         : 1.53
% 14.78/6.54  BG Simplification    : 0.11
% 14.78/6.55  Subsumption          : 1.74
% 14.78/6.55  Abstraction          : 0.20
% 14.78/6.55  MUC search           : 0.00
% 14.78/6.55  Cooper               : 0.00
% 14.78/6.55  Total                : 5.83
% 14.78/6.55  Index Insertion      : 0.00
% 14.78/6.55  Index Deletion       : 0.00
% 14.78/6.55  Index Matching       : 0.00
% 14.78/6.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
