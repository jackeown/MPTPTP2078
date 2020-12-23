%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:02 EST 2020

% Result     : Theorem 4.50s
% Output     : CNFRefutation 4.72s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 683 expanded)
%              Number of leaves         :   40 ( 255 expanded)
%              Depth                    :   14
%              Number of atoms          :  161 (1988 expanded)
%              Number of equality atoms :   36 ( 241 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v1_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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

tff(f_132,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_pre_topc(C,A)
               => ( v4_pre_topc(B,A)
                 => ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                     => ( D = B
                       => v4_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_2)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_61,axiom,(
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

tff(f_82,axiom,(
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

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_35,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_114,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => ( v4_pre_topc(C,B)
              <=> ? [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                    & v4_pre_topc(D,A)
                    & k9_subset_1(u1_struct_0(B),D,k2_struct_0(B)) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_pre_topc)).

tff(c_64,plain,(
    ~ v4_pre_topc('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_72,plain,(
    m1_pre_topc('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_68,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_76,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_94,plain,(
    ! [B_102,A_103] :
      ( l1_pre_topc(B_102)
      | ~ m1_pre_topc(B_102,A_103)
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_97,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_94])).

tff(c_100,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_97])).

tff(c_288,plain,(
    ! [A_129,B_130] :
      ( m1_pre_topc(k1_pre_topc(A_129,B_130),A_129)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_295,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_7','#skF_8'),'#skF_7')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_288])).

tff(c_305,plain,(
    m1_pre_topc(k1_pre_topc('#skF_7','#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_295])).

tff(c_54,plain,(
    ! [B_66,A_64] :
      ( l1_pre_topc(B_66)
      | ~ m1_pre_topc(B_66,A_64)
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_315,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_7','#skF_8'))
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_305,c_54])).

tff(c_318,plain,(
    l1_pre_topc(k1_pre_topc('#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_315])).

tff(c_159,plain,(
    ! [A_114,B_115] :
      ( v1_pre_topc(k1_pre_topc(A_114,B_115))
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_169,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_7','#skF_8'))
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_159])).

tff(c_180,plain,(
    v1_pre_topc(k1_pre_topc('#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_169])).

tff(c_631,plain,(
    ! [A_176,B_177] :
      ( k2_struct_0(k1_pre_topc(A_176,B_177)) = B_177
      | ~ m1_pre_topc(k1_pre_topc(A_176,B_177),A_176)
      | ~ v1_pre_topc(k1_pre_topc(A_176,B_177))
      | ~ m1_subset_1(B_177,k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ l1_pre_topc(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_637,plain,
    ( k2_struct_0(k1_pre_topc('#skF_7','#skF_8')) = '#skF_8'
    | ~ v1_pre_topc(k1_pre_topc('#skF_7','#skF_8'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7')))
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_305,c_631])).

tff(c_646,plain,(
    k2_struct_0(k1_pre_topc('#skF_7','#skF_8')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_68,c_180,c_637])).

tff(c_396,plain,(
    ! [B_138,A_139] :
      ( r1_tarski(k2_struct_0(B_138),k2_struct_0(A_139))
      | ~ m1_pre_topc(B_138,A_139)
      | ~ l1_pre_topc(B_138)
      | ~ l1_pre_topc(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_403,plain,(
    ! [B_138,A_139] :
      ( k3_xboole_0(k2_struct_0(B_138),k2_struct_0(A_139)) = k2_struct_0(B_138)
      | ~ m1_pre_topc(B_138,A_139)
      | ~ l1_pre_topc(B_138)
      | ~ l1_pre_topc(A_139) ) ),
    inference(resolution,[status(thm)],[c_396,c_2])).

tff(c_682,plain,(
    ! [A_139] :
      ( k3_xboole_0('#skF_8',k2_struct_0(A_139)) = k2_struct_0(k1_pre_topc('#skF_7','#skF_8'))
      | ~ m1_pre_topc(k1_pre_topc('#skF_7','#skF_8'),A_139)
      | ~ l1_pre_topc(k1_pre_topc('#skF_7','#skF_8'))
      | ~ l1_pre_topc(A_139) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_646,c_403])).

tff(c_927,plain,(
    ! [A_187] :
      ( k3_xboole_0('#skF_8',k2_struct_0(A_187)) = '#skF_8'
      | ~ m1_pre_topc(k1_pre_topc('#skF_7','#skF_8'),A_187)
      | ~ l1_pre_topc(A_187) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_646,c_682])).

tff(c_930,plain,
    ( k3_xboole_0('#skF_8',k2_struct_0('#skF_7')) = '#skF_8'
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_305,c_927])).

tff(c_933,plain,(
    k3_xboole_0('#skF_8',k2_struct_0('#skF_7')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_930])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_183,plain,(
    ! [A_117,B_118,C_119] :
      ( k9_subset_1(A_117,B_118,C_119) = k3_xboole_0(B_118,C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(A_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_192,plain,(
    ! [B_14,B_118,A_13] :
      ( k9_subset_1(B_14,B_118,A_13) = k3_xboole_0(B_118,A_13)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(resolution,[status(thm)],[c_16,c_183])).

tff(c_402,plain,(
    ! [A_139,B_118,B_138] :
      ( k9_subset_1(k2_struct_0(A_139),B_118,k2_struct_0(B_138)) = k3_xboole_0(B_118,k2_struct_0(B_138))
      | ~ m1_pre_topc(B_138,A_139)
      | ~ l1_pre_topc(B_138)
      | ~ l1_pre_topc(A_139) ) ),
    inference(resolution,[status(thm)],[c_396,c_192])).

tff(c_676,plain,(
    ! [A_139,B_118] :
      ( k9_subset_1(k2_struct_0(A_139),B_118,'#skF_8') = k3_xboole_0(B_118,k2_struct_0(k1_pre_topc('#skF_7','#skF_8')))
      | ~ m1_pre_topc(k1_pre_topc('#skF_7','#skF_8'),A_139)
      | ~ l1_pre_topc(k1_pre_topc('#skF_7','#skF_8'))
      | ~ l1_pre_topc(A_139) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_646,c_402])).

tff(c_1078,plain,(
    ! [A_199,B_200] :
      ( k9_subset_1(k2_struct_0(A_199),B_200,'#skF_8') = k3_xboole_0(B_200,'#skF_8')
      | ~ m1_pre_topc(k1_pre_topc('#skF_7','#skF_8'),A_199)
      | ~ l1_pre_topc(A_199) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_646,c_676])).

tff(c_1080,plain,(
    ! [B_200] :
      ( k9_subset_1(k2_struct_0('#skF_7'),B_200,'#skF_8') = k3_xboole_0(B_200,'#skF_8')
      | ~ l1_pre_topc('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_305,c_1078])).

tff(c_1084,plain,(
    ! [B_201] : k9_subset_1(k2_struct_0('#skF_7'),B_201,'#skF_8') = k3_xboole_0(B_201,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_1080])).

tff(c_6,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_79,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_195,plain,(
    ! [A_7,B_118] : k9_subset_1(A_7,B_118,A_7) = k3_xboole_0(B_118,A_7) ),
    inference(resolution,[status(thm)],[c_79,c_183])).

tff(c_223,plain,(
    ! [A_124,C_125,B_126] :
      ( k9_subset_1(A_124,C_125,B_126) = k9_subset_1(A_124,B_126,C_125)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(A_124)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_231,plain,(
    ! [A_7,B_126] : k9_subset_1(A_7,B_126,A_7) = k9_subset_1(A_7,A_7,B_126) ),
    inference(resolution,[status(thm)],[c_79,c_223])).

tff(c_238,plain,(
    ! [A_7,B_126] : k9_subset_1(A_7,A_7,B_126) = k3_xboole_0(B_126,A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_231])).

tff(c_1091,plain,(
    k3_xboole_0(k2_struct_0('#skF_7'),'#skF_8') = k3_xboole_0('#skF_8',k2_struct_0('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1084,c_238])).

tff(c_1100,plain,(
    k3_xboole_0(k2_struct_0('#skF_7'),'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_933,c_1091])).

tff(c_194,plain,(
    ! [B_118] : k9_subset_1(u1_struct_0('#skF_7'),B_118,'#skF_8') = k3_xboole_0(B_118,'#skF_8') ),
    inference(resolution,[status(thm)],[c_68,c_183])).

tff(c_229,plain,(
    ! [B_126] : k9_subset_1(u1_struct_0('#skF_7'),B_126,'#skF_8') = k9_subset_1(u1_struct_0('#skF_7'),'#skF_8',B_126) ),
    inference(resolution,[status(thm)],[c_68,c_223])).

tff(c_236,plain,(
    ! [B_126] : k9_subset_1(u1_struct_0('#skF_7'),'#skF_8',B_126) = k3_xboole_0(B_126,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_229])).

tff(c_66,plain,(
    '#skF_6' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_70,plain,(
    v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_77,plain,(
    v4_pre_topc('#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70])).

tff(c_74,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_78,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_74])).

tff(c_2127,plain,(
    ! [B_264,D_265,A_266] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(B_264),D_265,k2_struct_0(B_264)),B_264)
      | ~ v4_pre_topc(D_265,A_266)
      | ~ m1_subset_1(D_265,k1_zfmisc_1(u1_struct_0(A_266)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_264),D_265,k2_struct_0(B_264)),k1_zfmisc_1(u1_struct_0(B_264)))
      | ~ m1_pre_topc(B_264,A_266)
      | ~ l1_pre_topc(A_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2140,plain,(
    ! [B_264] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(B_264),'#skF_8',k2_struct_0(B_264)),B_264)
      | ~ v4_pre_topc('#skF_8','#skF_5')
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_264),'#skF_8',k2_struct_0(B_264)),k1_zfmisc_1(u1_struct_0(B_264)))
      | ~ m1_pre_topc(B_264,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_78,c_2127])).

tff(c_2168,plain,(
    ! [B_270] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(B_270),'#skF_8',k2_struct_0(B_270)),B_270)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_270),'#skF_8',k2_struct_0(B_270)),k1_zfmisc_1(u1_struct_0(B_270)))
      | ~ m1_pre_topc(B_270,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_77,c_2140])).

tff(c_2185,plain,
    ( v4_pre_topc(k9_subset_1(u1_struct_0('#skF_7'),'#skF_8',k2_struct_0('#skF_7')),'#skF_7')
    | ~ m1_subset_1(k3_xboole_0(k2_struct_0('#skF_7'),'#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_7')))
    | ~ m1_pre_topc('#skF_7','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_2168])).

tff(c_2195,plain,(
    v4_pre_topc('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_1100,c_1100,c_236,c_2185])).

tff(c_2197,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2195])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:30:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.50/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.50/1.80  
% 4.50/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.50/1.80  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v1_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2
% 4.50/1.80  
% 4.50/1.80  %Foreground sorts:
% 4.50/1.80  
% 4.50/1.80  
% 4.50/1.80  %Background operators:
% 4.50/1.80  
% 4.50/1.80  
% 4.50/1.80  %Foreground operators:
% 4.50/1.80  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 4.50/1.80  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.50/1.80  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.50/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.50/1.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.50/1.80  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.50/1.80  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.50/1.80  tff('#skF_7', type, '#skF_7': $i).
% 4.50/1.80  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.50/1.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.50/1.80  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.50/1.80  tff('#skF_5', type, '#skF_5': $i).
% 4.50/1.80  tff('#skF_6', type, '#skF_6': $i).
% 4.50/1.80  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.50/1.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.50/1.80  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.50/1.80  tff('#skF_8', type, '#skF_8': $i).
% 4.50/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.50/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.50/1.80  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.50/1.80  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.50/1.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.50/1.80  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.50/1.80  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.50/1.80  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.50/1.80  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.50/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.50/1.80  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.50/1.80  
% 4.72/1.82  tff(f_132, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v4_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v4_pre_topc(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tops_2)).
% 4.72/1.82  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.72/1.82  tff(f_90, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 4.72/1.82  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((v1_pre_topc(C) & m1_pre_topc(C, A)) => ((C = k1_pre_topc(A, B)) <=> (k2_struct_0(C) = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_pre_topc)).
% 4.72/1.82  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(B, A) <=> (r1_tarski(k2_struct_0(B), k2_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (r2_hidden(C, u1_pre_topc(B)) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(D, u1_pre_topc(A))) & (C = k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_pre_topc)).
% 4.72/1.82  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.72/1.82  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.72/1.82  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.72/1.82  tff(f_35, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.72/1.82  tff(f_37, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.72/1.82  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 4.72/1.82  tff(f_114, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (v4_pre_topc(C, B) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v4_pre_topc(D, A)) & (k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)) = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_pre_topc)).
% 4.72/1.82  tff(c_64, plain, (~v4_pre_topc('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.72/1.82  tff(c_72, plain, (m1_pre_topc('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.72/1.82  tff(c_68, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_7')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.72/1.82  tff(c_76, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.72/1.82  tff(c_94, plain, (![B_102, A_103]: (l1_pre_topc(B_102) | ~m1_pre_topc(B_102, A_103) | ~l1_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.72/1.82  tff(c_97, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_72, c_94])).
% 4.72/1.82  tff(c_100, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_97])).
% 4.72/1.82  tff(c_288, plain, (![A_129, B_130]: (m1_pre_topc(k1_pre_topc(A_129, B_130), A_129) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_pre_topc(A_129))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.72/1.82  tff(c_295, plain, (m1_pre_topc(k1_pre_topc('#skF_7', '#skF_8'), '#skF_7') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_68, c_288])).
% 4.72/1.82  tff(c_305, plain, (m1_pre_topc(k1_pre_topc('#skF_7', '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_295])).
% 4.72/1.82  tff(c_54, plain, (![B_66, A_64]: (l1_pre_topc(B_66) | ~m1_pre_topc(B_66, A_64) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.72/1.82  tff(c_315, plain, (l1_pre_topc(k1_pre_topc('#skF_7', '#skF_8')) | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_305, c_54])).
% 4.72/1.82  tff(c_318, plain, (l1_pre_topc(k1_pre_topc('#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_315])).
% 4.72/1.82  tff(c_159, plain, (![A_114, B_115]: (v1_pre_topc(k1_pre_topc(A_114, B_115)) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.72/1.82  tff(c_169, plain, (v1_pre_topc(k1_pre_topc('#skF_7', '#skF_8')) | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_68, c_159])).
% 4.72/1.82  tff(c_180, plain, (v1_pre_topc(k1_pre_topc('#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_169])).
% 4.72/1.82  tff(c_631, plain, (![A_176, B_177]: (k2_struct_0(k1_pre_topc(A_176, B_177))=B_177 | ~m1_pre_topc(k1_pre_topc(A_176, B_177), A_176) | ~v1_pre_topc(k1_pre_topc(A_176, B_177)) | ~m1_subset_1(B_177, k1_zfmisc_1(u1_struct_0(A_176))) | ~l1_pre_topc(A_176))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.72/1.82  tff(c_637, plain, (k2_struct_0(k1_pre_topc('#skF_7', '#skF_8'))='#skF_8' | ~v1_pre_topc(k1_pre_topc('#skF_7', '#skF_8')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_305, c_631])).
% 4.72/1.82  tff(c_646, plain, (k2_struct_0(k1_pre_topc('#skF_7', '#skF_8'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_68, c_180, c_637])).
% 4.72/1.82  tff(c_396, plain, (![B_138, A_139]: (r1_tarski(k2_struct_0(B_138), k2_struct_0(A_139)) | ~m1_pre_topc(B_138, A_139) | ~l1_pre_topc(B_138) | ~l1_pre_topc(A_139))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.72/1.82  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.72/1.82  tff(c_403, plain, (![B_138, A_139]: (k3_xboole_0(k2_struct_0(B_138), k2_struct_0(A_139))=k2_struct_0(B_138) | ~m1_pre_topc(B_138, A_139) | ~l1_pre_topc(B_138) | ~l1_pre_topc(A_139))), inference(resolution, [status(thm)], [c_396, c_2])).
% 4.72/1.82  tff(c_682, plain, (![A_139]: (k3_xboole_0('#skF_8', k2_struct_0(A_139))=k2_struct_0(k1_pre_topc('#skF_7', '#skF_8')) | ~m1_pre_topc(k1_pre_topc('#skF_7', '#skF_8'), A_139) | ~l1_pre_topc(k1_pre_topc('#skF_7', '#skF_8')) | ~l1_pre_topc(A_139))), inference(superposition, [status(thm), theory('equality')], [c_646, c_403])).
% 4.72/1.82  tff(c_927, plain, (![A_187]: (k3_xboole_0('#skF_8', k2_struct_0(A_187))='#skF_8' | ~m1_pre_topc(k1_pre_topc('#skF_7', '#skF_8'), A_187) | ~l1_pre_topc(A_187))), inference(demodulation, [status(thm), theory('equality')], [c_318, c_646, c_682])).
% 4.72/1.82  tff(c_930, plain, (k3_xboole_0('#skF_8', k2_struct_0('#skF_7'))='#skF_8' | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_305, c_927])).
% 4.72/1.82  tff(c_933, plain, (k3_xboole_0('#skF_8', k2_struct_0('#skF_7'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_930])).
% 4.72/1.82  tff(c_16, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.72/1.82  tff(c_183, plain, (![A_117, B_118, C_119]: (k9_subset_1(A_117, B_118, C_119)=k3_xboole_0(B_118, C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(A_117)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.72/1.82  tff(c_192, plain, (![B_14, B_118, A_13]: (k9_subset_1(B_14, B_118, A_13)=k3_xboole_0(B_118, A_13) | ~r1_tarski(A_13, B_14))), inference(resolution, [status(thm)], [c_16, c_183])).
% 4.72/1.82  tff(c_402, plain, (![A_139, B_118, B_138]: (k9_subset_1(k2_struct_0(A_139), B_118, k2_struct_0(B_138))=k3_xboole_0(B_118, k2_struct_0(B_138)) | ~m1_pre_topc(B_138, A_139) | ~l1_pre_topc(B_138) | ~l1_pre_topc(A_139))), inference(resolution, [status(thm)], [c_396, c_192])).
% 4.72/1.82  tff(c_676, plain, (![A_139, B_118]: (k9_subset_1(k2_struct_0(A_139), B_118, '#skF_8')=k3_xboole_0(B_118, k2_struct_0(k1_pre_topc('#skF_7', '#skF_8'))) | ~m1_pre_topc(k1_pre_topc('#skF_7', '#skF_8'), A_139) | ~l1_pre_topc(k1_pre_topc('#skF_7', '#skF_8')) | ~l1_pre_topc(A_139))), inference(superposition, [status(thm), theory('equality')], [c_646, c_402])).
% 4.72/1.82  tff(c_1078, plain, (![A_199, B_200]: (k9_subset_1(k2_struct_0(A_199), B_200, '#skF_8')=k3_xboole_0(B_200, '#skF_8') | ~m1_pre_topc(k1_pre_topc('#skF_7', '#skF_8'), A_199) | ~l1_pre_topc(A_199))), inference(demodulation, [status(thm), theory('equality')], [c_318, c_646, c_676])).
% 4.72/1.82  tff(c_1080, plain, (![B_200]: (k9_subset_1(k2_struct_0('#skF_7'), B_200, '#skF_8')=k3_xboole_0(B_200, '#skF_8') | ~l1_pre_topc('#skF_7'))), inference(resolution, [status(thm)], [c_305, c_1078])).
% 4.72/1.82  tff(c_1084, plain, (![B_201]: (k9_subset_1(k2_struct_0('#skF_7'), B_201, '#skF_8')=k3_xboole_0(B_201, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_1080])).
% 4.72/1.82  tff(c_6, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.72/1.82  tff(c_8, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.72/1.82  tff(c_79, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 4.72/1.82  tff(c_195, plain, (![A_7, B_118]: (k9_subset_1(A_7, B_118, A_7)=k3_xboole_0(B_118, A_7))), inference(resolution, [status(thm)], [c_79, c_183])).
% 4.72/1.82  tff(c_223, plain, (![A_124, C_125, B_126]: (k9_subset_1(A_124, C_125, B_126)=k9_subset_1(A_124, B_126, C_125) | ~m1_subset_1(C_125, k1_zfmisc_1(A_124)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.72/1.82  tff(c_231, plain, (![A_7, B_126]: (k9_subset_1(A_7, B_126, A_7)=k9_subset_1(A_7, A_7, B_126))), inference(resolution, [status(thm)], [c_79, c_223])).
% 4.72/1.82  tff(c_238, plain, (![A_7, B_126]: (k9_subset_1(A_7, A_7, B_126)=k3_xboole_0(B_126, A_7))), inference(demodulation, [status(thm), theory('equality')], [c_195, c_231])).
% 4.72/1.82  tff(c_1091, plain, (k3_xboole_0(k2_struct_0('#skF_7'), '#skF_8')=k3_xboole_0('#skF_8', k2_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1084, c_238])).
% 4.72/1.82  tff(c_1100, plain, (k3_xboole_0(k2_struct_0('#skF_7'), '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_933, c_1091])).
% 4.72/1.82  tff(c_194, plain, (![B_118]: (k9_subset_1(u1_struct_0('#skF_7'), B_118, '#skF_8')=k3_xboole_0(B_118, '#skF_8'))), inference(resolution, [status(thm)], [c_68, c_183])).
% 4.72/1.82  tff(c_229, plain, (![B_126]: (k9_subset_1(u1_struct_0('#skF_7'), B_126, '#skF_8')=k9_subset_1(u1_struct_0('#skF_7'), '#skF_8', B_126))), inference(resolution, [status(thm)], [c_68, c_223])).
% 4.72/1.82  tff(c_236, plain, (![B_126]: (k9_subset_1(u1_struct_0('#skF_7'), '#skF_8', B_126)=k3_xboole_0(B_126, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_229])).
% 4.72/1.82  tff(c_66, plain, ('#skF_6'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.72/1.82  tff(c_70, plain, (v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.72/1.82  tff(c_77, plain, (v4_pre_topc('#skF_8', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70])).
% 4.72/1.82  tff(c_74, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.72/1.82  tff(c_78, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_74])).
% 4.72/1.82  tff(c_2127, plain, (![B_264, D_265, A_266]: (v4_pre_topc(k9_subset_1(u1_struct_0(B_264), D_265, k2_struct_0(B_264)), B_264) | ~v4_pre_topc(D_265, A_266) | ~m1_subset_1(D_265, k1_zfmisc_1(u1_struct_0(A_266))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_264), D_265, k2_struct_0(B_264)), k1_zfmisc_1(u1_struct_0(B_264))) | ~m1_pre_topc(B_264, A_266) | ~l1_pre_topc(A_266))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.72/1.82  tff(c_2140, plain, (![B_264]: (v4_pre_topc(k9_subset_1(u1_struct_0(B_264), '#skF_8', k2_struct_0(B_264)), B_264) | ~v4_pre_topc('#skF_8', '#skF_5') | ~m1_subset_1(k9_subset_1(u1_struct_0(B_264), '#skF_8', k2_struct_0(B_264)), k1_zfmisc_1(u1_struct_0(B_264))) | ~m1_pre_topc(B_264, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_78, c_2127])).
% 4.72/1.82  tff(c_2168, plain, (![B_270]: (v4_pre_topc(k9_subset_1(u1_struct_0(B_270), '#skF_8', k2_struct_0(B_270)), B_270) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_270), '#skF_8', k2_struct_0(B_270)), k1_zfmisc_1(u1_struct_0(B_270))) | ~m1_pre_topc(B_270, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_77, c_2140])).
% 4.72/1.82  tff(c_2185, plain, (v4_pre_topc(k9_subset_1(u1_struct_0('#skF_7'), '#skF_8', k2_struct_0('#skF_7')), '#skF_7') | ~m1_subset_1(k3_xboole_0(k2_struct_0('#skF_7'), '#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~m1_pre_topc('#skF_7', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_236, c_2168])).
% 4.72/1.82  tff(c_2195, plain, (v4_pre_topc('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_1100, c_1100, c_236, c_2185])).
% 4.72/1.82  tff(c_2197, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_2195])).
% 4.72/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.72/1.82  
% 4.72/1.82  Inference rules
% 4.72/1.82  ----------------------
% 4.72/1.82  #Ref     : 0
% 4.72/1.82  #Sup     : 469
% 4.72/1.82  #Fact    : 0
% 4.72/1.82  #Define  : 0
% 4.72/1.82  #Split   : 5
% 4.72/1.82  #Chain   : 0
% 4.72/1.82  #Close   : 0
% 4.72/1.82  
% 4.72/1.82  Ordering : KBO
% 4.72/1.82  
% 4.72/1.82  Simplification rules
% 4.72/1.82  ----------------------
% 4.72/1.82  #Subsume      : 41
% 4.72/1.82  #Demod        : 363
% 4.72/1.82  #Tautology    : 199
% 4.72/1.82  #SimpNegUnit  : 1
% 4.72/1.82  #BackRed      : 0
% 4.72/1.82  
% 4.72/1.82  #Partial instantiations: 0
% 4.72/1.82  #Strategies tried      : 1
% 4.72/1.82  
% 4.72/1.82  Timing (in seconds)
% 4.72/1.82  ----------------------
% 4.72/1.82  Preprocessing        : 0.33
% 4.72/1.82  Parsing              : 0.17
% 4.72/1.82  CNF conversion       : 0.03
% 4.72/1.82  Main loop            : 0.70
% 4.72/1.82  Inferencing          : 0.24
% 4.72/1.82  Reduction            : 0.25
% 4.72/1.82  Demodulation         : 0.19
% 4.72/1.82  BG Simplification    : 0.04
% 4.72/1.82  Subsumption          : 0.13
% 4.72/1.82  Abstraction          : 0.04
% 4.72/1.82  MUC search           : 0.00
% 4.72/1.82  Cooper               : 0.00
% 4.72/1.82  Total                : 1.07
% 4.72/1.82  Index Insertion      : 0.00
% 4.72/1.82  Index Deletion       : 0.00
% 4.72/1.82  Index Matching       : 0.00
% 4.72/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
