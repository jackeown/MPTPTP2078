%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT2070+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:50 EST 2020

% Result     : Theorem 17.11s
% Output     : CNFRefutation 17.23s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 463 expanded)
%              Number of leaves         :   34 ( 177 expanded)
%              Depth                    :   29
%              Number of atoms          :  532 (2248 expanded)
%              Number of equality atoms :   13 (  28 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_7 > v4_pre_topc > v3_waybel_7 > v2_waybel_0 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k3_yellow_1 > k2_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(r2_waybel_7,type,(
    r2_waybel_7: ( $i * $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(v3_waybel_7,type,(
    v3_waybel_7: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_141,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> ! [C] :
                  ( ( ~ v1_xboole_0(C)
                    & v2_waybel_0(C,k3_yellow_1(k2_struct_0(A)))
                    & v13_waybel_0(C,k3_yellow_1(k2_struct_0(A)))
                    & v3_waybel_7(C,k3_yellow_1(k2_struct_0(A)))
                    & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
                 => ( r2_hidden(B,C)
                   => ! [D] :
                        ( m1_subset_1(D,u1_struct_0(A))
                       => ( r2_waybel_7(A,C,D)
                         => r2_hidden(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_yellow19)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_30,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_74,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(C,k2_pre_topc(A,B))
              <=> ? [D] :
                    ( ~ v1_xboole_0(D)
                    & v2_waybel_0(D,k3_yellow_1(k2_struct_0(A)))
                    & v13_waybel_0(D,k3_yellow_1(k2_struct_0(A)))
                    & v3_waybel_7(D,k3_yellow_1(k2_struct_0(A)))
                    & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))
                    & r2_hidden(B,D)
                    & r2_waybel_7(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_yellow19)).

tff(f_102,axiom,(
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

tff(c_66,plain,
    ( ~ v1_xboole_0('#skF_5')
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_91,plain,(
    ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_46,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_136,plain,(
    ! [B_88,A_89] :
      ( r1_tarski(B_88,k2_pre_topc(A_89,B_88))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_138,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_136])).

tff(c_141,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_138])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_148,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ r1_tarski(k2_pre_topc('#skF_3','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_141,c_2])).

tff(c_151,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(k2_pre_topc(A_8,B_9),k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_186,plain,(
    ! [A_98,B_99] :
      ( m1_subset_1(k2_pre_topc(A_98,B_99),k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_32,plain,(
    ! [B_34,A_32] :
      ( r1_tarski(B_34,k2_pre_topc(A_32,B_34))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_195,plain,(
    ! [A_98,B_99] :
      ( r1_tarski(k2_pre_topc(A_98,B_99),k2_pre_topc(A_98,k2_pre_topc(A_98,B_99)))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98) ) ),
    inference(resolution,[status(thm)],[c_186,c_32])).

tff(c_327,plain,(
    ! [A_115,B_116] :
      ( r1_tarski(k2_pre_topc(A_115,B_116),k2_pre_topc(A_115,k2_pre_topc(A_115,B_116)))
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(resolution,[status(thm)],[c_186,c_32])).

tff(c_12,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_127,plain,(
    ! [C_81,B_82,A_83] :
      ( r2_hidden(C_81,B_82)
      | ~ r2_hidden(C_81,A_83)
      | ~ r1_tarski(A_83,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_156,plain,(
    ! [A_90,B_91,B_92] :
      ( r2_hidden('#skF_1'(A_90,B_91),B_92)
      | ~ r1_tarski(A_90,B_92)
      | r1_tarski(A_90,B_91) ) ),
    inference(resolution,[status(thm)],[c_12,c_127])).

tff(c_8,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_166,plain,(
    ! [A_90,B_91,B_4,B_92] :
      ( r2_hidden('#skF_1'(A_90,B_91),B_4)
      | ~ r1_tarski(B_92,B_4)
      | ~ r1_tarski(A_90,B_92)
      | r1_tarski(A_90,B_91) ) ),
    inference(resolution,[status(thm)],[c_156,c_8])).

tff(c_854,plain,(
    ! [A_210,B_211,A_212,B_213] :
      ( r2_hidden('#skF_1'(A_210,B_211),k2_pre_topc(A_212,k2_pre_topc(A_212,B_213)))
      | ~ r1_tarski(A_210,k2_pre_topc(A_212,B_213))
      | r1_tarski(A_210,B_211)
      | ~ m1_subset_1(B_213,k1_zfmisc_1(u1_struct_0(A_212)))
      | ~ l1_pre_topc(A_212) ) ),
    inference(resolution,[status(thm)],[c_327,c_166])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_876,plain,(
    ! [A_214,A_215,B_216] :
      ( ~ r1_tarski(A_214,k2_pre_topc(A_215,B_216))
      | r1_tarski(A_214,k2_pre_topc(A_215,k2_pre_topc(A_215,B_216)))
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0(A_215)))
      | ~ l1_pre_topc(A_215) ) ),
    inference(resolution,[status(thm)],[c_854,c_10])).

tff(c_197,plain,(
    ! [A_100,B_101,B_102,B_103] :
      ( r2_hidden('#skF_1'(A_100,B_101),B_102)
      | ~ r1_tarski(B_103,B_102)
      | ~ r1_tarski(A_100,B_103)
      | r1_tarski(A_100,B_101) ) ),
    inference(resolution,[status(thm)],[c_156,c_8])).

tff(c_207,plain,(
    ! [A_104,B_105] :
      ( r2_hidden('#skF_1'(A_104,B_105),k2_pre_topc('#skF_3','#skF_4'))
      | ~ r1_tarski(A_104,'#skF_4')
      | r1_tarski(A_104,B_105) ) ),
    inference(resolution,[status(thm)],[c_141,c_197])).

tff(c_435,plain,(
    ! [A_132,B_133,B_134] :
      ( r2_hidden('#skF_1'(A_132,B_133),B_134)
      | ~ r1_tarski(k2_pre_topc('#skF_3','#skF_4'),B_134)
      | ~ r1_tarski(A_132,'#skF_4')
      | r1_tarski(A_132,B_133) ) ),
    inference(resolution,[status(thm)],[c_207,c_8])).

tff(c_458,plain,(
    ! [B_134,A_132] :
      ( ~ r1_tarski(k2_pre_topc('#skF_3','#skF_4'),B_134)
      | ~ r1_tarski(A_132,'#skF_4')
      | r1_tarski(A_132,B_134) ) ),
    inference(resolution,[status(thm)],[c_435,c_10])).

tff(c_1024,plain,(
    ! [A_237,A_238,B_239] :
      ( ~ r1_tarski(A_237,'#skF_4')
      | r1_tarski(A_237,k2_pre_topc(A_238,k2_pre_topc(A_238,B_239)))
      | ~ r1_tarski(k2_pre_topc('#skF_3','#skF_4'),k2_pre_topc(A_238,B_239))
      | ~ m1_subset_1(B_239,k1_zfmisc_1(u1_struct_0(A_238)))
      | ~ l1_pre_topc(A_238) ) ),
    inference(resolution,[status(thm)],[c_876,c_458])).

tff(c_1033,plain,(
    ! [A_237] :
      ( ~ r1_tarski(A_237,'#skF_4')
      | r1_tarski(A_237,k2_pre_topc('#skF_3',k2_pre_topc('#skF_3',k2_pre_topc('#skF_3','#skF_4'))))
      | ~ m1_subset_1(k2_pre_topc('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_195,c_1024])).

tff(c_1049,plain,(
    ! [A_237] :
      ( ~ r1_tarski(A_237,'#skF_4')
      | r1_tarski(A_237,k2_pre_topc('#skF_3',k2_pre_topc('#skF_3',k2_pre_topc('#skF_3','#skF_4'))))
      | ~ m1_subset_1(k2_pre_topc('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1033])).

tff(c_1057,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1049])).

tff(c_1060,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_1057])).

tff(c_1064,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1060])).

tff(c_1066,plain,(
    m1_subset_1(k2_pre_topc('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1049])).

tff(c_1083,plain,
    ( r1_tarski(k2_pre_topc('#skF_3','#skF_4'),k2_pre_topc('#skF_3',k2_pre_topc('#skF_3','#skF_4')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1066,c_32])).

tff(c_1108,plain,(
    r1_tarski(k2_pre_topc('#skF_3','#skF_4'),k2_pre_topc('#skF_3',k2_pre_topc('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1083])).

tff(c_130,plain,(
    ! [A_3,B_4,B_82] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_82)
      | ~ r1_tarski(A_3,B_82)
      | r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_12,c_127])).

tff(c_34,plain,(
    ! [A_35,C_37,B_36] :
      ( m1_subset_1(A_35,C_37)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(C_37))
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_377,plain,(
    ! [A_122,A_123,B_124] :
      ( m1_subset_1(A_122,u1_struct_0(A_123))
      | ~ r2_hidden(A_122,k2_pre_topc(A_123,B_124))
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123) ) ),
    inference(resolution,[status(thm)],[c_186,c_34])).

tff(c_747,plain,(
    ! [A_182,B_183,A_184,B_185] :
      ( m1_subset_1('#skF_1'(A_182,B_183),u1_struct_0(A_184))
      | ~ m1_subset_1(B_185,k1_zfmisc_1(u1_struct_0(A_184)))
      | ~ l1_pre_topc(A_184)
      | ~ r1_tarski(A_182,k2_pre_topc(A_184,B_185))
      | r1_tarski(A_182,B_183) ) ),
    inference(resolution,[status(thm)],[c_130,c_377])).

tff(c_752,plain,(
    ! [A_182,B_183,A_8,B_9] :
      ( m1_subset_1('#skF_1'(A_182,B_183),u1_struct_0(A_8))
      | ~ r1_tarski(A_182,k2_pre_topc(A_8,k2_pre_topc(A_8,B_9)))
      | r1_tarski(A_182,B_183)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(resolution,[status(thm)],[c_14,c_747])).

tff(c_1115,plain,(
    ! [B_183] :
      ( m1_subset_1('#skF_1'(k2_pre_topc('#skF_3','#skF_4'),B_183),u1_struct_0('#skF_3'))
      | r1_tarski(k2_pre_topc('#skF_3','#skF_4'),B_183)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1108,c_752])).

tff(c_1149,plain,(
    ! [B_183] :
      ( m1_subset_1('#skF_1'(k2_pre_topc('#skF_3','#skF_4'),B_183),u1_struct_0('#skF_3'))
      | r1_tarski(k2_pre_topc('#skF_3','#skF_4'),B_183) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1115])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_751,plain,(
    ! [A_182,B_183] :
      ( m1_subset_1('#skF_1'(A_182,B_183),u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_182,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_182,B_183) ) ),
    inference(resolution,[status(thm)],[c_42,c_747])).

tff(c_755,plain,(
    ! [A_182,B_183] :
      ( m1_subset_1('#skF_1'(A_182,B_183),u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_182,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_182,B_183) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_751])).

tff(c_416,plain,(
    ! [B_129,A_130,C_131] :
      ( r2_hidden(B_129,'#skF_2'(A_130,B_129,C_131))
      | ~ r2_hidden(C_131,k2_pre_topc(A_130,B_129))
      | ~ m1_subset_1(C_131,u1_struct_0(A_130))
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130)
      | ~ v2_pre_topc(A_130)
      | v2_struct_0(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_433,plain,(
    ! [B_129,A_130,A_3,B_4] :
      ( r2_hidden(B_129,'#skF_2'(A_130,B_129,'#skF_1'(A_3,B_4)))
      | ~ m1_subset_1('#skF_1'(A_3,B_4),u1_struct_0(A_130))
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130)
      | ~ v2_pre_topc(A_130)
      | v2_struct_0(A_130)
      | ~ r1_tarski(A_3,k2_pre_topc(A_130,B_129))
      | r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_130,c_416])).

tff(c_26,plain,(
    ! [A_10,B_22,C_28] :
      ( v13_waybel_0('#skF_2'(A_10,B_22,C_28),k3_yellow_1(k2_struct_0(A_10)))
      | ~ r2_hidden(C_28,k2_pre_topc(A_10,B_22))
      | ~ m1_subset_1(C_28,u1_struct_0(A_10))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_28,plain,(
    ! [A_10,B_22,C_28] :
      ( v2_waybel_0('#skF_2'(A_10,B_22,C_28),k3_yellow_1(k2_struct_0(A_10)))
      | ~ r2_hidden(C_28,k2_pre_topc(A_10,B_22))
      | ~ m1_subset_1(C_28,u1_struct_0(A_10))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24,plain,(
    ! [A_10,B_22,C_28] :
      ( v3_waybel_7('#skF_2'(A_10,B_22,C_28),k3_yellow_1(k2_struct_0(A_10)))
      | ~ r2_hidden(C_28,k2_pre_topc(A_10,B_22))
      | ~ m1_subset_1(C_28,u1_struct_0(A_10))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_22,plain,(
    ! [A_10,B_22,C_28] :
      ( m1_subset_1('#skF_2'(A_10,B_22,C_28),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_10)))))
      | ~ r2_hidden(C_28,k2_pre_topc(A_10,B_22))
      | ~ m1_subset_1(C_28,u1_struct_0(A_10))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_591,plain,(
    ! [A_146,B_147,C_148] :
      ( r2_waybel_7(A_146,'#skF_2'(A_146,B_147,C_148),C_148)
      | ~ r2_hidden(C_148,k2_pre_topc(A_146,B_147))
      | ~ m1_subset_1(C_148,u1_struct_0(A_146))
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ l1_pre_topc(A_146)
      | ~ v2_pre_topc(A_146)
      | v2_struct_0(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_595,plain,(
    ! [C_148] :
      ( r2_waybel_7('#skF_3','#skF_2'('#skF_3','#skF_4',C_148),C_148)
      | ~ r2_hidden(C_148,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_148,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_42,c_591])).

tff(c_599,plain,(
    ! [C_148] :
      ( r2_waybel_7('#skF_3','#skF_2'('#skF_3','#skF_4',C_148),C_148)
      | ~ r2_hidden(C_148,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_148,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_595])).

tff(c_601,plain,(
    ! [C_149] :
      ( r2_waybel_7('#skF_3','#skF_2'('#skF_3','#skF_4',C_149),C_149)
      | ~ r2_hidden(C_149,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_149,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_599])).

tff(c_88,plain,(
    ! [D_65,C_63] :
      ( v4_pre_topc('#skF_4','#skF_3')
      | r2_hidden(D_65,'#skF_4')
      | ~ r2_waybel_7('#skF_3',C_63,D_65)
      | ~ m1_subset_1(D_65,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_4',C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
      | ~ v3_waybel_7(C_63,k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v13_waybel_0(C_63,k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0(C_63,k3_yellow_1(k2_struct_0('#skF_3')))
      | v1_xboole_0(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_375,plain,(
    ! [D_65,C_63] :
      ( r2_hidden(D_65,'#skF_4')
      | ~ r2_waybel_7('#skF_3',C_63,D_65)
      | ~ m1_subset_1(D_65,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_4',C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
      | ~ v3_waybel_7(C_63,k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v13_waybel_0(C_63,k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0(C_63,k3_yellow_1(k2_struct_0('#skF_3')))
      | v1_xboole_0(C_63) ) ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_88])).

tff(c_7169,plain,(
    ! [C_450] :
      ( r2_hidden(C_450,'#skF_4')
      | ~ r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_4',C_450))
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4',C_450),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
      | ~ v3_waybel_7('#skF_2'('#skF_3','#skF_4',C_450),k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v13_waybel_0('#skF_2'('#skF_3','#skF_4',C_450),k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_2'('#skF_3','#skF_4',C_450),k3_yellow_1(k2_struct_0('#skF_3')))
      | v1_xboole_0('#skF_2'('#skF_3','#skF_4',C_450))
      | ~ r2_hidden(C_450,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_450,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_601,c_375])).

tff(c_7173,plain,(
    ! [C_28] :
      ( r2_hidden(C_28,'#skF_4')
      | ~ r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_4',C_28))
      | ~ v3_waybel_7('#skF_2'('#skF_3','#skF_4',C_28),k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v13_waybel_0('#skF_2'('#skF_3','#skF_4',C_28),k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_2'('#skF_3','#skF_4',C_28),k3_yellow_1(k2_struct_0('#skF_3')))
      | v1_xboole_0('#skF_2'('#skF_3','#skF_4',C_28))
      | ~ r2_hidden(C_28,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_28,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_7169])).

tff(c_7176,plain,(
    ! [C_28] :
      ( r2_hidden(C_28,'#skF_4')
      | ~ r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_4',C_28))
      | ~ v3_waybel_7('#skF_2'('#skF_3','#skF_4',C_28),k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v13_waybel_0('#skF_2'('#skF_3','#skF_4',C_28),k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_2'('#skF_3','#skF_4',C_28),k3_yellow_1(k2_struct_0('#skF_3')))
      | v1_xboole_0('#skF_2'('#skF_3','#skF_4',C_28))
      | ~ r2_hidden(C_28,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_28,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_7173])).

tff(c_18417,plain,(
    ! [C_711] :
      ( r2_hidden(C_711,'#skF_4')
      | ~ r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_4',C_711))
      | ~ v3_waybel_7('#skF_2'('#skF_3','#skF_4',C_711),k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v13_waybel_0('#skF_2'('#skF_3','#skF_4',C_711),k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_2'('#skF_3','#skF_4',C_711),k3_yellow_1(k2_struct_0('#skF_3')))
      | v1_xboole_0('#skF_2'('#skF_3','#skF_4',C_711))
      | ~ r2_hidden(C_711,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_711,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_7176])).

tff(c_18421,plain,(
    ! [C_28] :
      ( r2_hidden(C_28,'#skF_4')
      | ~ r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_4',C_28))
      | ~ v13_waybel_0('#skF_2'('#skF_3','#skF_4',C_28),k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_2'('#skF_3','#skF_4',C_28),k3_yellow_1(k2_struct_0('#skF_3')))
      | v1_xboole_0('#skF_2'('#skF_3','#skF_4',C_28))
      | ~ r2_hidden(C_28,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_28,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_18417])).

tff(c_18424,plain,(
    ! [C_28] :
      ( r2_hidden(C_28,'#skF_4')
      | ~ r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_4',C_28))
      | ~ v13_waybel_0('#skF_2'('#skF_3','#skF_4',C_28),k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_2'('#skF_3','#skF_4',C_28),k3_yellow_1(k2_struct_0('#skF_3')))
      | v1_xboole_0('#skF_2'('#skF_3','#skF_4',C_28))
      | ~ r2_hidden(C_28,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_28,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_18421])).

tff(c_32478,plain,(
    ! [C_1025] :
      ( r2_hidden(C_1025,'#skF_4')
      | ~ r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_4',C_1025))
      | ~ v13_waybel_0('#skF_2'('#skF_3','#skF_4',C_1025),k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_2'('#skF_3','#skF_4',C_1025),k3_yellow_1(k2_struct_0('#skF_3')))
      | v1_xboole_0('#skF_2'('#skF_3','#skF_4',C_1025))
      | ~ r2_hidden(C_1025,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_1025,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_18424])).

tff(c_32482,plain,(
    ! [C_28] :
      ( r2_hidden(C_28,'#skF_4')
      | ~ r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_4',C_28))
      | ~ v13_waybel_0('#skF_2'('#skF_3','#skF_4',C_28),k3_yellow_1(k2_struct_0('#skF_3')))
      | v1_xboole_0('#skF_2'('#skF_3','#skF_4',C_28))
      | ~ r2_hidden(C_28,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_28,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_32478])).

tff(c_32485,plain,(
    ! [C_28] :
      ( r2_hidden(C_28,'#skF_4')
      | ~ r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_4',C_28))
      | ~ v13_waybel_0('#skF_2'('#skF_3','#skF_4',C_28),k3_yellow_1(k2_struct_0('#skF_3')))
      | v1_xboole_0('#skF_2'('#skF_3','#skF_4',C_28))
      | ~ r2_hidden(C_28,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_28,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_32482])).

tff(c_32659,plain,(
    ! [C_1029] :
      ( r2_hidden(C_1029,'#skF_4')
      | ~ r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_4',C_1029))
      | ~ v13_waybel_0('#skF_2'('#skF_3','#skF_4',C_1029),k3_yellow_1(k2_struct_0('#skF_3')))
      | v1_xboole_0('#skF_2'('#skF_3','#skF_4',C_1029))
      | ~ r2_hidden(C_1029,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_1029,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_32485])).

tff(c_32663,plain,(
    ! [C_28] :
      ( r2_hidden(C_28,'#skF_4')
      | ~ r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_4',C_28))
      | v1_xboole_0('#skF_2'('#skF_3','#skF_4',C_28))
      | ~ r2_hidden(C_28,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_28,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_32659])).

tff(c_32666,plain,(
    ! [C_28] :
      ( r2_hidden(C_28,'#skF_4')
      | ~ r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_4',C_28))
      | v1_xboole_0('#skF_2'('#skF_3','#skF_4',C_28))
      | ~ r2_hidden(C_28,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_28,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_32663])).

tff(c_32668,plain,(
    ! [C_1030] :
      ( r2_hidden(C_1030,'#skF_4')
      | ~ r2_hidden('#skF_4','#skF_2'('#skF_3','#skF_4',C_1030))
      | v1_xboole_0('#skF_2'('#skF_3','#skF_4',C_1030))
      | ~ r2_hidden(C_1030,k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_1030,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_32666])).

tff(c_32673,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),'#skF_4')
      | v1_xboole_0('#skF_2'('#skF_3','#skF_4','#skF_1'(A_3,B_4)))
      | ~ r2_hidden('#skF_1'(A_3,B_4),k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_1'(A_3,B_4),u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_3,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_433,c_32668])).

tff(c_32690,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),'#skF_4')
      | v1_xboole_0('#skF_2'('#skF_3','#skF_4','#skF_1'(A_3,B_4)))
      | ~ r2_hidden('#skF_1'(A_3,B_4),k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_1'(A_3,B_4),u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_3,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_3,B_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_32673])).

tff(c_33842,plain,(
    ! [A_1040,B_1041] :
      ( r2_hidden('#skF_1'(A_1040,B_1041),'#skF_4')
      | v1_xboole_0('#skF_2'('#skF_3','#skF_4','#skF_1'(A_1040,B_1041)))
      | ~ r2_hidden('#skF_1'(A_1040,B_1041),k2_pre_topc('#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_1'(A_1040,B_1041),u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_1040,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_1040,B_1041) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_32690])).

tff(c_35828,plain,(
    ! [A_1085,B_1086] :
      ( r2_hidden('#skF_1'(A_1085,B_1086),'#skF_4')
      | v1_xboole_0('#skF_2'('#skF_3','#skF_4','#skF_1'(A_1085,B_1086)))
      | ~ m1_subset_1('#skF_1'(A_1085,B_1086),u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_1085,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_1085,B_1086) ) ),
    inference(resolution,[status(thm)],[c_130,c_33842])).

tff(c_35883,plain,(
    ! [A_1087,B_1088] :
      ( r2_hidden('#skF_1'(A_1087,B_1088),'#skF_4')
      | v1_xboole_0('#skF_2'('#skF_3','#skF_4','#skF_1'(A_1087,B_1088)))
      | ~ r1_tarski(A_1087,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_1087,B_1088) ) ),
    inference(resolution,[status(thm)],[c_755,c_35828])).

tff(c_351,plain,(
    ! [A_117,B_118,C_119] :
      ( ~ v1_xboole_0('#skF_2'(A_117,B_118,C_119))
      | ~ r2_hidden(C_119,k2_pre_topc(A_117,B_118))
      | ~ m1_subset_1(C_119,u1_struct_0(A_117))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117)
      | ~ v2_pre_topc(A_117)
      | v2_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_368,plain,(
    ! [A_117,B_118,A_3,B_4] :
      ( ~ v1_xboole_0('#skF_2'(A_117,B_118,'#skF_1'(A_3,B_4)))
      | ~ m1_subset_1('#skF_1'(A_3,B_4),u1_struct_0(A_117))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117)
      | ~ v2_pre_topc(A_117)
      | v2_struct_0(A_117)
      | ~ r1_tarski(A_3,k2_pre_topc(A_117,B_118))
      | r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_130,c_351])).

tff(c_35891,plain,(
    ! [A_1087,B_1088] :
      ( ~ m1_subset_1('#skF_1'(A_1087,B_1088),u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | r2_hidden('#skF_1'(A_1087,B_1088),'#skF_4')
      | ~ r1_tarski(A_1087,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_1087,B_1088) ) ),
    inference(resolution,[status(thm)],[c_35883,c_368])).

tff(c_35905,plain,(
    ! [A_1087,B_1088] :
      ( ~ m1_subset_1('#skF_1'(A_1087,B_1088),u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | r2_hidden('#skF_1'(A_1087,B_1088),'#skF_4')
      | ~ r1_tarski(A_1087,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_1087,B_1088) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_35891])).

tff(c_35913,plain,(
    ! [A_1089,B_1090] :
      ( ~ m1_subset_1('#skF_1'(A_1089,B_1090),u1_struct_0('#skF_3'))
      | r2_hidden('#skF_1'(A_1089,B_1090),'#skF_4')
      | ~ r1_tarski(A_1089,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(A_1089,B_1090) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_35905])).

tff(c_35931,plain,(
    ! [B_183] :
      ( r2_hidden('#skF_1'(k2_pre_topc('#skF_3','#skF_4'),B_183),'#skF_4')
      | ~ r1_tarski(k2_pre_topc('#skF_3','#skF_4'),k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski(k2_pre_topc('#skF_3','#skF_4'),B_183) ) ),
    inference(resolution,[status(thm)],[c_1149,c_35913])).

tff(c_35968,plain,(
    ! [B_1091] :
      ( r2_hidden('#skF_1'(k2_pre_topc('#skF_3','#skF_4'),B_1091),'#skF_4')
      | r1_tarski(k2_pre_topc('#skF_3','#skF_4'),B_1091) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_35931])).

tff(c_35976,plain,(
    r1_tarski(k2_pre_topc('#skF_3','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_35968,c_10])).

tff(c_35987,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_151,c_35976])).

tff(c_35988,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_36082,plain,(
    ! [B_1110,A_1111] :
      ( v4_pre_topc(B_1110,A_1111)
      | k2_pre_topc(A_1111,B_1110) != B_1110
      | ~ v2_pre_topc(A_1111)
      | ~ m1_subset_1(B_1110,k1_zfmisc_1(u1_struct_0(A_1111)))
      | ~ l1_pre_topc(A_1111) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_36088,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != '#skF_4'
    | ~ v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_36082])).

tff(c_36092,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_35988,c_36088])).

tff(c_36094,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_36092])).

tff(c_36096,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_50,plain,
    ( ~ r2_hidden('#skF_6','#skF_4')
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_36105,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36096,c_50])).

tff(c_56,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_36099,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36096,c_56])).

tff(c_36243,plain,(
    ! [A_1146,B_1147] :
      ( k2_pre_topc(A_1146,B_1147) = B_1147
      | ~ v4_pre_topc(B_1147,A_1146)
      | ~ m1_subset_1(B_1147,k1_zfmisc_1(u1_struct_0(A_1146)))
      | ~ l1_pre_topc(A_1146) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_36249,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_36243])).

tff(c_36253,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36096,c_36249])).

tff(c_36207,plain,(
    ! [B_1141,A_1142] :
      ( r1_tarski(B_1141,k2_pre_topc(A_1142,B_1141))
      | ~ m1_subset_1(B_1141,k1_zfmisc_1(u1_struct_0(A_1142)))
      | ~ l1_pre_topc(A_1142) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_36211,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_36207])).

tff(c_36215,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36211])).

tff(c_36225,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ r1_tarski(k2_pre_topc('#skF_3','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_36215,c_2])).

tff(c_36242,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_36225])).

tff(c_36262,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_36253,c_36242])).

tff(c_36263,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_36225])).

tff(c_36095,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_54,plain,
    ( m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_36109,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36096,c_54])).

tff(c_64,plain,
    ( v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_36114,plain,(
    v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36096,c_64])).

tff(c_62,plain,
    ( v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_36128,plain,(
    v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36096,c_62])).

tff(c_60,plain,
    ( v3_waybel_7('#skF_5',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_36112,plain,(
    v3_waybel_7('#skF_5',k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36096,c_60])).

tff(c_58,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_36177,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36096,c_58])).

tff(c_52,plain,
    ( r2_waybel_7('#skF_3','#skF_5','#skF_6')
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_36107,plain,(
    r2_waybel_7('#skF_3','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36096,c_52])).

tff(c_37354,plain,(
    ! [C_1332,A_1333,B_1334,D_1335] :
      ( r2_hidden(C_1332,k2_pre_topc(A_1333,B_1334))
      | ~ r2_waybel_7(A_1333,D_1335,C_1332)
      | ~ r2_hidden(B_1334,D_1335)
      | ~ m1_subset_1(D_1335,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_1333)))))
      | ~ v3_waybel_7(D_1335,k3_yellow_1(k2_struct_0(A_1333)))
      | ~ v13_waybel_0(D_1335,k3_yellow_1(k2_struct_0(A_1333)))
      | ~ v2_waybel_0(D_1335,k3_yellow_1(k2_struct_0(A_1333)))
      | v1_xboole_0(D_1335)
      | ~ m1_subset_1(C_1332,u1_struct_0(A_1333))
      | ~ m1_subset_1(B_1334,k1_zfmisc_1(u1_struct_0(A_1333)))
      | ~ l1_pre_topc(A_1333)
      | ~ v2_pre_topc(A_1333)
      | v2_struct_0(A_1333) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_37360,plain,(
    ! [B_1334] :
      ( r2_hidden('#skF_6',k2_pre_topc('#skF_3',B_1334))
      | ~ r2_hidden(B_1334,'#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))
      | ~ v3_waybel_7('#skF_5',k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_3')))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_3')))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_1334,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36107,c_37354])).

tff(c_37368,plain,(
    ! [B_1334] :
      ( r2_hidden('#skF_6',k2_pre_topc('#skF_3',B_1334))
      | ~ r2_hidden(B_1334,'#skF_5')
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(B_1334,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_36109,c_36114,c_36128,c_36112,c_36177,c_37360])).

tff(c_37370,plain,(
    ! [B_1336] :
      ( r2_hidden('#skF_6',k2_pre_topc('#skF_3',B_1336))
      | ~ r2_hidden(B_1336,'#skF_5')
      | ~ m1_subset_1(B_1336,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_36095,c_37368])).

tff(c_37377,plain,
    ( r2_hidden('#skF_6',k2_pre_topc('#skF_3','#skF_4'))
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_37370])).

tff(c_37383,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36099,c_36263,c_37377])).

tff(c_37385,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36105,c_37383])).

%------------------------------------------------------------------------------
