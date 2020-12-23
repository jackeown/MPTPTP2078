%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:07 EST 2020

% Result     : Theorem 24.66s
% Output     : CNFRefutation 24.66s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 163 expanded)
%              Number of leaves         :   30 (  72 expanded)
%              Depth                    :   13
%              Number of atoms          :  110 ( 392 expanded)
%              Number of equality atoms :   15 (  46 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > l1_pre_topc > k9_subset_1 > k1_tops_2 > k3_xboole_0 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_tops_2,type,(
    k1_tops_2: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
                   => ( r2_hidden(B,D)
                     => r2_hidden(k9_subset_1(u1_struct_0(A),B,C),k1_tops_2(A,C,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tops_2)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) )
     => m1_subset_1(k1_tops_2(A,B,C),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A,B))))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_2)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A,B)))))
                 => ( D = k1_tops_2(A,B,C)
                  <=> ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(k1_pre_topc(A,B))))
                       => ( r2_hidden(E,D)
                        <=> ? [F] :
                              ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(A)))
                              & r2_hidden(F,C)
                              & k9_subset_1(u1_struct_0(A),F,B) = E ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_2)).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_46,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_48,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_54,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_184,plain,(
    ! [A_228,B_229] :
      ( u1_struct_0(k1_pre_topc(A_228,B_229)) = B_229
      | ~ m1_subset_1(B_229,k1_zfmisc_1(u1_struct_0(A_228)))
      | ~ l1_pre_topc(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_194,plain,
    ( u1_struct_0(k1_pre_topc('#skF_4','#skF_6')) = '#skF_6'
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_184])).

tff(c_208,plain,(
    u1_struct_0(k1_pre_topc('#skF_4','#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_194])).

tff(c_349,plain,(
    ! [A_241,B_242,C_243] :
      ( m1_subset_1(k1_tops_2(A_241,B_242,C_243),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_241,B_242)))))
      | ~ m1_subset_1(C_243,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_241))))
      | ~ m1_subset_1(B_242,k1_zfmisc_1(u1_struct_0(A_241)))
      | ~ l1_pre_topc(A_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_362,plain,(
    ! [C_243] :
      ( m1_subset_1(k1_tops_2('#skF_4','#skF_6',C_243),k1_zfmisc_1(k1_zfmisc_1('#skF_6')))
      | ~ m1_subset_1(C_243,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_349])).

tff(c_370,plain,(
    ! [C_243] :
      ( m1_subset_1(k1_tops_2('#skF_4','#skF_6',C_243),k1_zfmisc_1(k1_zfmisc_1('#skF_6')))
      | ~ m1_subset_1(C_243,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_362])).

tff(c_969,plain,(
    ! [C_311] :
      ( m1_subset_1(k1_tops_2('#skF_4','#skF_6',C_311),k1_zfmisc_1(k1_zfmisc_1('#skF_6')))
      | ~ m1_subset_1(C_311,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_362])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8] :
      ( k9_subset_1(A_6,B_7,C_8) = k3_xboole_0(B_7,C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4033,plain,(
    ! [B_470,C_471] :
      ( k9_subset_1(k1_zfmisc_1('#skF_6'),B_470,k1_tops_2('#skF_4','#skF_6',C_471)) = k3_xboole_0(B_470,k1_tops_2('#skF_4','#skF_6',C_471))
      | ~ m1_subset_1(C_471,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ) ),
    inference(resolution,[status(thm)],[c_969,c_8])).

tff(c_4076,plain,(
    ! [B_472] : k9_subset_1(k1_zfmisc_1('#skF_6'),B_472,k1_tops_2('#skF_4','#skF_6','#skF_7')) = k3_xboole_0(B_472,k1_tops_2('#skF_4','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_48,c_4033])).

tff(c_6,plain,(
    ! [A_3,B_4,C_5] :
      ( m1_subset_1(k9_subset_1(A_3,B_4,C_5),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(C_5,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4085,plain,(
    ! [B_472] :
      ( m1_subset_1(k3_xboole_0(B_472,k1_tops_2('#skF_4','#skF_6','#skF_7')),k1_zfmisc_1(k1_zfmisc_1('#skF_6')))
      | ~ m1_subset_1(k1_tops_2('#skF_4','#skF_6','#skF_7'),k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4076,c_6])).

tff(c_4228,plain,(
    ~ m1_subset_1(k1_tops_2('#skF_4','#skF_6','#skF_7'),k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_4085])).

tff(c_4232,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_370,c_4228])).

tff(c_4236,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4232])).

tff(c_4238,plain,(
    m1_subset_1(k1_tops_2('#skF_4','#skF_6','#skF_7'),k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_4085])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_55,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_99,plain,(
    ! [A_215,B_216,C_217] :
      ( k9_subset_1(A_215,B_216,C_217) = k3_xboole_0(B_216,C_217)
      | ~ m1_subset_1(C_217,k1_zfmisc_1(A_215)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_114,plain,(
    ! [A_2,B_216] : k9_subset_1(A_2,B_216,A_2) = k3_xboole_0(B_216,A_2) ),
    inference(resolution,[status(thm)],[c_55,c_99])).

tff(c_157,plain,(
    ! [A_225,B_226,C_227] :
      ( m1_subset_1(k9_subset_1(A_225,B_226,C_227),k1_zfmisc_1(A_225))
      | ~ m1_subset_1(C_227,k1_zfmisc_1(A_225)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_173,plain,(
    ! [B_216,A_2] :
      ( m1_subset_1(k3_xboole_0(B_216,A_2),k1_zfmisc_1(A_2))
      | ~ m1_subset_1(A_2,k1_zfmisc_1(A_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_157])).

tff(c_183,plain,(
    ! [B_216,A_2] : m1_subset_1(k3_xboole_0(B_216,A_2),k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_173])).

tff(c_112,plain,(
    ! [B_216] : k9_subset_1(u1_struct_0('#skF_4'),B_216,'#skF_6') = k3_xboole_0(B_216,'#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_99])).

tff(c_3804,plain,(
    ! [A_458,F_459,B_460,C_461] :
      ( r2_hidden(k9_subset_1(u1_struct_0(A_458),F_459,B_460),k1_tops_2(A_458,B_460,C_461))
      | ~ r2_hidden(F_459,C_461)
      | ~ m1_subset_1(F_459,k1_zfmisc_1(u1_struct_0(A_458)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(A_458),F_459,B_460),k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_458,B_460))))
      | ~ m1_subset_1(k1_tops_2(A_458,B_460,C_461),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_458,B_460)))))
      | ~ m1_subset_1(C_461,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_458))))
      | ~ m1_subset_1(B_460,k1_zfmisc_1(u1_struct_0(A_458)))
      | ~ l1_pre_topc(A_458) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_3911,plain,(
    ! [F_459,C_461] :
      ( r2_hidden(k9_subset_1(u1_struct_0('#skF_4'),F_459,'#skF_6'),k1_tops_2('#skF_4','#skF_6',C_461))
      | ~ r2_hidden(F_459,C_461)
      | ~ m1_subset_1(F_459,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0('#skF_4'),F_459,'#skF_6'),k1_zfmisc_1('#skF_6'))
      | ~ m1_subset_1(k1_tops_2('#skF_4','#skF_6',C_461),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_4','#skF_6')))))
      | ~ m1_subset_1(C_461,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_3804])).

tff(c_41227,plain,(
    ! [F_1489,C_1490] :
      ( r2_hidden(k3_xboole_0(F_1489,'#skF_6'),k1_tops_2('#skF_4','#skF_6',C_1490))
      | ~ r2_hidden(F_1489,C_1490)
      | ~ m1_subset_1(F_1489,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(k1_tops_2('#skF_4','#skF_6',C_1490),k1_zfmisc_1(k1_zfmisc_1('#skF_6')))
      | ~ m1_subset_1(C_1490,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_208,c_183,c_112,c_112,c_3911])).

tff(c_41234,plain,(
    ! [F_1489] :
      ( r2_hidden(k3_xboole_0(F_1489,'#skF_6'),k1_tops_2('#skF_4','#skF_6','#skF_7'))
      | ~ r2_hidden(F_1489,'#skF_7')
      | ~ m1_subset_1(F_1489,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ) ),
    inference(resolution,[status(thm)],[c_4238,c_41227])).

tff(c_41247,plain,(
    ! [F_1491] :
      ( r2_hidden(k3_xboole_0(F_1491,'#skF_6'),k1_tops_2('#skF_4','#skF_6','#skF_7'))
      | ~ r2_hidden(F_1491,'#skF_7')
      | ~ m1_subset_1(F_1491,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_41234])).

tff(c_44,plain,(
    ~ r2_hidden(k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_6'),k1_tops_2('#skF_4','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_124,plain,(
    ~ r2_hidden(k3_xboole_0('#skF_5','#skF_6'),k1_tops_2('#skF_4','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_44])).

tff(c_41261,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_41247,c_124])).

tff(c_41280,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_41261])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:57:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 24.66/13.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.66/13.47  
% 24.66/13.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.66/13.47  %$ r2_hidden > m1_subset_1 > l1_pre_topc > k9_subset_1 > k1_tops_2 > k3_xboole_0 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4 > #skF_3
% 24.66/13.47  
% 24.66/13.47  %Foreground sorts:
% 24.66/13.47  
% 24.66/13.47  
% 24.66/13.47  %Background operators:
% 24.66/13.47  
% 24.66/13.47  
% 24.66/13.47  %Foreground operators:
% 24.66/13.47  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 24.66/13.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 24.66/13.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 24.66/13.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 24.66/13.47  tff('#skF_7', type, '#skF_7': $i).
% 24.66/13.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 24.66/13.47  tff('#skF_5', type, '#skF_5': $i).
% 24.66/13.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 24.66/13.47  tff('#skF_6', type, '#skF_6': $i).
% 24.66/13.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 24.66/13.47  tff(k1_tops_2, type, k1_tops_2: ($i * $i * $i) > $i).
% 24.66/13.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 24.66/13.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 24.66/13.47  tff('#skF_4', type, '#skF_4': $i).
% 24.66/13.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 24.66/13.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 24.66/13.47  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 24.66/13.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 24.66/13.47  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 24.66/13.47  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 24.66/13.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 24.66/13.47  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 24.66/13.47  
% 24.66/13.49  tff(f_101, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r2_hidden(B, D) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), k1_tops_2(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tops_2)).
% 24.66/13.49  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_pre_topc)).
% 24.66/13.49  tff(f_85, axiom, (![A, B, C]: (((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))) => m1_subset_1(k1_tops_2(A, B, C), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_2)).
% 24.66/13.49  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 24.66/13.49  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 24.66/13.49  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 24.66/13.49  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 24.66/13.49  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A, B))))) => ((D = k1_tops_2(A, B, C)) <=> (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(k1_pre_topc(A, B)))) => (r2_hidden(E, D) <=> (?[F]: ((m1_subset_1(F, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(F, C)) & (k9_subset_1(u1_struct_0(A), F, B) = E))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_2)).
% 24.66/13.49  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 24.66/13.49  tff(c_46, plain, (r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_101])).
% 24.66/13.49  tff(c_48, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 24.66/13.49  tff(c_54, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 24.66/13.49  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 24.66/13.49  tff(c_184, plain, (![A_228, B_229]: (u1_struct_0(k1_pre_topc(A_228, B_229))=B_229 | ~m1_subset_1(B_229, k1_zfmisc_1(u1_struct_0(A_228))) | ~l1_pre_topc(A_228))), inference(cnfTransformation, [status(thm)], [f_52])).
% 24.66/13.49  tff(c_194, plain, (u1_struct_0(k1_pre_topc('#skF_4', '#skF_6'))='#skF_6' | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_50, c_184])).
% 24.66/13.49  tff(c_208, plain, (u1_struct_0(k1_pre_topc('#skF_4', '#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_194])).
% 24.66/13.49  tff(c_349, plain, (![A_241, B_242, C_243]: (m1_subset_1(k1_tops_2(A_241, B_242, C_243), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_241, B_242))))) | ~m1_subset_1(C_243, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_241)))) | ~m1_subset_1(B_242, k1_zfmisc_1(u1_struct_0(A_241))) | ~l1_pre_topc(A_241))), inference(cnfTransformation, [status(thm)], [f_85])).
% 24.66/13.49  tff(c_362, plain, (![C_243]: (m1_subset_1(k1_tops_2('#skF_4', '#skF_6', C_243), k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) | ~m1_subset_1(C_243, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_208, c_349])).
% 24.66/13.49  tff(c_370, plain, (![C_243]: (m1_subset_1(k1_tops_2('#skF_4', '#skF_6', C_243), k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) | ~m1_subset_1(C_243, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_362])).
% 24.66/13.49  tff(c_969, plain, (![C_311]: (m1_subset_1(k1_tops_2('#skF_4', '#skF_6', C_311), k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) | ~m1_subset_1(C_311, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_362])).
% 24.66/13.49  tff(c_8, plain, (![A_6, B_7, C_8]: (k9_subset_1(A_6, B_7, C_8)=k3_xboole_0(B_7, C_8) | ~m1_subset_1(C_8, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 24.66/13.49  tff(c_4033, plain, (![B_470, C_471]: (k9_subset_1(k1_zfmisc_1('#skF_6'), B_470, k1_tops_2('#skF_4', '#skF_6', C_471))=k3_xboole_0(B_470, k1_tops_2('#skF_4', '#skF_6', C_471)) | ~m1_subset_1(C_471, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))))), inference(resolution, [status(thm)], [c_969, c_8])).
% 24.66/13.49  tff(c_4076, plain, (![B_472]: (k9_subset_1(k1_zfmisc_1('#skF_6'), B_472, k1_tops_2('#skF_4', '#skF_6', '#skF_7'))=k3_xboole_0(B_472, k1_tops_2('#skF_4', '#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_48, c_4033])).
% 24.66/13.49  tff(c_6, plain, (![A_3, B_4, C_5]: (m1_subset_1(k9_subset_1(A_3, B_4, C_5), k1_zfmisc_1(A_3)) | ~m1_subset_1(C_5, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 24.66/13.49  tff(c_4085, plain, (![B_472]: (m1_subset_1(k3_xboole_0(B_472, k1_tops_2('#skF_4', '#skF_6', '#skF_7')), k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) | ~m1_subset_1(k1_tops_2('#skF_4', '#skF_6', '#skF_7'), k1_zfmisc_1(k1_zfmisc_1('#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_4076, c_6])).
% 24.66/13.49  tff(c_4228, plain, (~m1_subset_1(k1_tops_2('#skF_4', '#skF_6', '#skF_7'), k1_zfmisc_1(k1_zfmisc_1('#skF_6')))), inference(splitLeft, [status(thm)], [c_4085])).
% 24.66/13.49  tff(c_4232, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_370, c_4228])).
% 24.66/13.49  tff(c_4236, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_4232])).
% 24.66/13.49  tff(c_4238, plain, (m1_subset_1(k1_tops_2('#skF_4', '#skF_6', '#skF_7'), k1_zfmisc_1(k1_zfmisc_1('#skF_6')))), inference(splitRight, [status(thm)], [c_4085])).
% 24.66/13.49  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 24.66/13.49  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 24.66/13.49  tff(c_55, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 24.66/13.49  tff(c_99, plain, (![A_215, B_216, C_217]: (k9_subset_1(A_215, B_216, C_217)=k3_xboole_0(B_216, C_217) | ~m1_subset_1(C_217, k1_zfmisc_1(A_215)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 24.66/13.49  tff(c_114, plain, (![A_2, B_216]: (k9_subset_1(A_2, B_216, A_2)=k3_xboole_0(B_216, A_2))), inference(resolution, [status(thm)], [c_55, c_99])).
% 24.66/13.49  tff(c_157, plain, (![A_225, B_226, C_227]: (m1_subset_1(k9_subset_1(A_225, B_226, C_227), k1_zfmisc_1(A_225)) | ~m1_subset_1(C_227, k1_zfmisc_1(A_225)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 24.66/13.49  tff(c_173, plain, (![B_216, A_2]: (m1_subset_1(k3_xboole_0(B_216, A_2), k1_zfmisc_1(A_2)) | ~m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_157])).
% 24.66/13.49  tff(c_183, plain, (![B_216, A_2]: (m1_subset_1(k3_xboole_0(B_216, A_2), k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_173])).
% 24.66/13.49  tff(c_112, plain, (![B_216]: (k9_subset_1(u1_struct_0('#skF_4'), B_216, '#skF_6')=k3_xboole_0(B_216, '#skF_6'))), inference(resolution, [status(thm)], [c_50, c_99])).
% 24.66/13.49  tff(c_3804, plain, (![A_458, F_459, B_460, C_461]: (r2_hidden(k9_subset_1(u1_struct_0(A_458), F_459, B_460), k1_tops_2(A_458, B_460, C_461)) | ~r2_hidden(F_459, C_461) | ~m1_subset_1(F_459, k1_zfmisc_1(u1_struct_0(A_458))) | ~m1_subset_1(k9_subset_1(u1_struct_0(A_458), F_459, B_460), k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_458, B_460)))) | ~m1_subset_1(k1_tops_2(A_458, B_460, C_461), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_458, B_460))))) | ~m1_subset_1(C_461, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_458)))) | ~m1_subset_1(B_460, k1_zfmisc_1(u1_struct_0(A_458))) | ~l1_pre_topc(A_458))), inference(cnfTransformation, [status(thm)], [f_77])).
% 24.66/13.49  tff(c_3911, plain, (![F_459, C_461]: (r2_hidden(k9_subset_1(u1_struct_0('#skF_4'), F_459, '#skF_6'), k1_tops_2('#skF_4', '#skF_6', C_461)) | ~r2_hidden(F_459, C_461) | ~m1_subset_1(F_459, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k9_subset_1(u1_struct_0('#skF_4'), F_459, '#skF_6'), k1_zfmisc_1('#skF_6')) | ~m1_subset_1(k1_tops_2('#skF_4', '#skF_6', C_461), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_4', '#skF_6'))))) | ~m1_subset_1(C_461, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_208, c_3804])).
% 24.66/13.49  tff(c_41227, plain, (![F_1489, C_1490]: (r2_hidden(k3_xboole_0(F_1489, '#skF_6'), k1_tops_2('#skF_4', '#skF_6', C_1490)) | ~r2_hidden(F_1489, C_1490) | ~m1_subset_1(F_1489, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k1_tops_2('#skF_4', '#skF_6', C_1490), k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) | ~m1_subset_1(C_1490, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_208, c_183, c_112, c_112, c_3911])).
% 24.66/13.49  tff(c_41234, plain, (![F_1489]: (r2_hidden(k3_xboole_0(F_1489, '#skF_6'), k1_tops_2('#skF_4', '#skF_6', '#skF_7')) | ~r2_hidden(F_1489, '#skF_7') | ~m1_subset_1(F_1489, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))))), inference(resolution, [status(thm)], [c_4238, c_41227])).
% 24.66/13.49  tff(c_41247, plain, (![F_1491]: (r2_hidden(k3_xboole_0(F_1491, '#skF_6'), k1_tops_2('#skF_4', '#skF_6', '#skF_7')) | ~r2_hidden(F_1491, '#skF_7') | ~m1_subset_1(F_1491, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_41234])).
% 24.66/13.49  tff(c_44, plain, (~r2_hidden(k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_6'), k1_tops_2('#skF_4', '#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 24.66/13.49  tff(c_124, plain, (~r2_hidden(k3_xboole_0('#skF_5', '#skF_6'), k1_tops_2('#skF_4', '#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_44])).
% 24.66/13.49  tff(c_41261, plain, (~r2_hidden('#skF_5', '#skF_7') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_41247, c_124])).
% 24.66/13.49  tff(c_41280, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_41261])).
% 24.66/13.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.66/13.49  
% 24.66/13.49  Inference rules
% 24.66/13.49  ----------------------
% 24.66/13.49  #Ref     : 0
% 24.66/13.49  #Sup     : 10938
% 24.66/13.49  #Fact    : 0
% 24.66/13.49  #Define  : 0
% 24.66/13.49  #Split   : 17
% 24.66/13.49  #Chain   : 0
% 24.66/13.49  #Close   : 0
% 24.66/13.49  
% 24.66/13.49  Ordering : KBO
% 24.66/13.49  
% 24.66/13.49  Simplification rules
% 24.66/13.49  ----------------------
% 24.66/13.49  #Subsume      : 787
% 24.66/13.49  #Demod        : 8643
% 24.66/13.49  #Tautology    : 1853
% 24.66/13.49  #SimpNegUnit  : 2
% 24.66/13.49  #BackRed      : 30
% 24.66/13.49  
% 24.66/13.49  #Partial instantiations: 0
% 24.66/13.49  #Strategies tried      : 1
% 24.66/13.49  
% 24.66/13.49  Timing (in seconds)
% 24.66/13.49  ----------------------
% 24.66/13.49  Preprocessing        : 0.38
% 24.66/13.49  Parsing              : 0.19
% 24.66/13.49  CNF conversion       : 0.04
% 24.66/13.49  Main loop            : 12.29
% 24.66/13.49  Inferencing          : 2.18
% 24.66/13.49  Reduction            : 5.82
% 24.66/13.49  Demodulation         : 4.97
% 24.66/13.49  BG Simplification    : 0.46
% 24.66/13.49  Subsumption          : 3.33
% 24.66/13.49  Abstraction          : 0.68
% 24.66/13.49  MUC search           : 0.00
% 24.66/13.49  Cooper               : 0.00
% 24.66/13.49  Total                : 12.70
% 24.66/13.49  Index Insertion      : 0.00
% 24.66/13.49  Index Deletion       : 0.00
% 24.66/13.49  Index Matching       : 0.00
% 24.66/13.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
