%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:32 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 123 expanded)
%              Number of leaves         :   26 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :  116 ( 350 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ? [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
            & v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_62,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_85,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ~ ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ~ ( r1_tarski(B,C)
                      & v3_tex_2(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tex_2)).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_6,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_52,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,B_33)
      | ~ m1_subset_1(A_32,k1_zfmisc_1(B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_56,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(resolution,[status(thm)],[c_6,c_52])).

tff(c_30,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_28,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_26,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_57,plain,(
    ! [A_34] : r1_tarski(k1_xboole_0,A_34) ),
    inference(resolution,[status(thm)],[c_6,c_52])).

tff(c_36,plain,(
    ! [A_29] :
      ( v1_xboole_0(A_29)
      | r2_hidden('#skF_1'(A_29),A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( ~ r1_tarski(B_12,A_11)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_43,plain,(
    ! [A_29] :
      ( ~ r1_tarski(A_29,'#skF_1'(A_29))
      | v1_xboole_0(A_29) ) ),
    inference(resolution,[status(thm)],[c_36,c_14])).

tff(c_62,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_57,c_43])).

tff(c_96,plain,(
    ! [B_46,A_47] :
      ( v2_tex_2(B_46,A_47)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ v1_xboole_0(B_46)
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_104,plain,(
    ! [A_47] :
      ( v2_tex_2(k1_xboole_0,A_47)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_6,c_96])).

tff(c_108,plain,(
    ! [A_47] :
      ( v2_tex_2(k1_xboole_0,A_47)
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_104])).

tff(c_431,plain,(
    ! [A_85,B_86] :
      ( m1_subset_1('#skF_2'(A_85,B_86),k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ v2_tex_2(B_86,A_85)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85)
      | ~ v3_tdlat_3(A_85)
      | ~ v2_pre_topc(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_24,plain,(
    ! [B_23] :
      ( ~ v3_tex_2(B_23,'#skF_3')
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_447,plain,(
    ! [B_86] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_86),'#skF_3')
      | ~ v2_tex_2(B_86,'#skF_3')
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_431,c_24])).

tff(c_455,plain,(
    ! [B_86] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_86),'#skF_3')
      | ~ v2_tex_2(B_86,'#skF_3')
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_447])).

tff(c_457,plain,(
    ! [B_87] :
      ( ~ v3_tex_2('#skF_2'('#skF_3',B_87),'#skF_3')
      | ~ v2_tex_2(B_87,'#skF_3')
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_455])).

tff(c_490,plain,
    ( ~ v3_tex_2('#skF_2'('#skF_3',k1_xboole_0),'#skF_3')
    | ~ v2_tex_2(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_457])).

tff(c_491,plain,(
    ~ v2_tex_2(k1_xboole_0,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_490])).

tff(c_494,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_108,c_491])).

tff(c_497,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_494])).

tff(c_499,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_497])).

tff(c_501,plain,(
    v2_tex_2(k1_xboole_0,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_490])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_153,plain,(
    ! [A_54,B_55] :
      ( v3_tex_2('#skF_2'(A_54,B_55),A_54)
      | ~ v2_tex_2(B_55,A_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54)
      | ~ v3_tdlat_3(A_54)
      | ~ v2_pre_topc(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_164,plain,(
    ! [A_54,A_6] :
      ( v3_tex_2('#skF_2'(A_54,A_6),A_54)
      | ~ v2_tex_2(A_6,A_54)
      | ~ l1_pre_topc(A_54)
      | ~ v3_tdlat_3(A_54)
      | ~ v2_pre_topc(A_54)
      | v2_struct_0(A_54)
      | ~ r1_tarski(A_6,u1_struct_0(A_54)) ) ),
    inference(resolution,[status(thm)],[c_10,c_153])).

tff(c_500,plain,(
    ~ v3_tex_2('#skF_2'('#skF_3',k1_xboole_0),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_490])).

tff(c_512,plain,
    ( ~ v2_tex_2(k1_xboole_0,'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ r1_tarski(k1_xboole_0,u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_164,c_500])).

tff(c_518,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_30,c_28,c_26,c_501,c_512])).

tff(c_520,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_518])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:58:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.64/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.39  
% 2.64/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.39  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 2.64/1.39  
% 2.64/1.39  %Foreground sorts:
% 2.64/1.39  
% 2.64/1.39  
% 2.64/1.39  %Background operators:
% 2.64/1.39  
% 2.64/1.39  
% 2.64/1.39  %Foreground operators:
% 2.64/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.64/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.64/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.64/1.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.64/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.64/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.64/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.64/1.39  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.64/1.39  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.64/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.64/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.64/1.39  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.64/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.64/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.64/1.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.64/1.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.64/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.64/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.64/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.64/1.39  
% 2.64/1.41  tff(f_100, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tex_2)).
% 2.64/1.41  tff(f_33, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.64/1.41  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.64/1.41  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.64/1.41  tff(f_48, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.64/1.41  tff(f_62, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 2.64/1.41  tff(f_85, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tex_2)).
% 2.64/1.41  tff(c_32, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.64/1.41  tff(c_6, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.64/1.41  tff(c_52, plain, (![A_32, B_33]: (r1_tarski(A_32, B_33) | ~m1_subset_1(A_32, k1_zfmisc_1(B_33)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.64/1.41  tff(c_56, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(resolution, [status(thm)], [c_6, c_52])).
% 2.64/1.41  tff(c_30, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.64/1.41  tff(c_28, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.64/1.41  tff(c_26, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.64/1.41  tff(c_57, plain, (![A_34]: (r1_tarski(k1_xboole_0, A_34))), inference(resolution, [status(thm)], [c_6, c_52])).
% 2.64/1.41  tff(c_36, plain, (![A_29]: (v1_xboole_0(A_29) | r2_hidden('#skF_1'(A_29), A_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.64/1.41  tff(c_14, plain, (![B_12, A_11]: (~r1_tarski(B_12, A_11) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.64/1.41  tff(c_43, plain, (![A_29]: (~r1_tarski(A_29, '#skF_1'(A_29)) | v1_xboole_0(A_29))), inference(resolution, [status(thm)], [c_36, c_14])).
% 2.64/1.41  tff(c_62, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_57, c_43])).
% 2.64/1.41  tff(c_96, plain, (![B_46, A_47]: (v2_tex_2(B_46, A_47) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_47))) | ~v1_xboole_0(B_46) | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.64/1.41  tff(c_104, plain, (![A_47]: (v2_tex_2(k1_xboole_0, A_47) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47) | v2_struct_0(A_47))), inference(resolution, [status(thm)], [c_6, c_96])).
% 2.64/1.41  tff(c_108, plain, (![A_47]: (v2_tex_2(k1_xboole_0, A_47) | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47) | v2_struct_0(A_47))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_104])).
% 2.64/1.41  tff(c_431, plain, (![A_85, B_86]: (m1_subset_1('#skF_2'(A_85, B_86), k1_zfmisc_1(u1_struct_0(A_85))) | ~v2_tex_2(B_86, A_85) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85) | ~v3_tdlat_3(A_85) | ~v2_pre_topc(A_85) | v2_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.64/1.41  tff(c_24, plain, (![B_23]: (~v3_tex_2(B_23, '#skF_3') | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.64/1.41  tff(c_447, plain, (![B_86]: (~v3_tex_2('#skF_2'('#skF_3', B_86), '#skF_3') | ~v2_tex_2(B_86, '#skF_3') | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_431, c_24])).
% 2.64/1.41  tff(c_455, plain, (![B_86]: (~v3_tex_2('#skF_2'('#skF_3', B_86), '#skF_3') | ~v2_tex_2(B_86, '#skF_3') | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_447])).
% 2.64/1.41  tff(c_457, plain, (![B_87]: (~v3_tex_2('#skF_2'('#skF_3', B_87), '#skF_3') | ~v2_tex_2(B_87, '#skF_3') | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_32, c_455])).
% 2.64/1.41  tff(c_490, plain, (~v3_tex_2('#skF_2'('#skF_3', k1_xboole_0), '#skF_3') | ~v2_tex_2(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_6, c_457])).
% 2.64/1.41  tff(c_491, plain, (~v2_tex_2(k1_xboole_0, '#skF_3')), inference(splitLeft, [status(thm)], [c_490])).
% 2.64/1.41  tff(c_494, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_108, c_491])).
% 2.64/1.41  tff(c_497, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_494])).
% 2.64/1.41  tff(c_499, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_497])).
% 2.64/1.41  tff(c_501, plain, (v2_tex_2(k1_xboole_0, '#skF_3')), inference(splitRight, [status(thm)], [c_490])).
% 2.64/1.41  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.64/1.41  tff(c_153, plain, (![A_54, B_55]: (v3_tex_2('#skF_2'(A_54, B_55), A_54) | ~v2_tex_2(B_55, A_54) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54) | ~v3_tdlat_3(A_54) | ~v2_pre_topc(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.64/1.41  tff(c_164, plain, (![A_54, A_6]: (v3_tex_2('#skF_2'(A_54, A_6), A_54) | ~v2_tex_2(A_6, A_54) | ~l1_pre_topc(A_54) | ~v3_tdlat_3(A_54) | ~v2_pre_topc(A_54) | v2_struct_0(A_54) | ~r1_tarski(A_6, u1_struct_0(A_54)))), inference(resolution, [status(thm)], [c_10, c_153])).
% 2.64/1.41  tff(c_500, plain, (~v3_tex_2('#skF_2'('#skF_3', k1_xboole_0), '#skF_3')), inference(splitRight, [status(thm)], [c_490])).
% 2.64/1.41  tff(c_512, plain, (~v2_tex_2(k1_xboole_0, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski(k1_xboole_0, u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_164, c_500])).
% 2.64/1.41  tff(c_518, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_30, c_28, c_26, c_501, c_512])).
% 2.64/1.41  tff(c_520, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_518])).
% 2.64/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.41  
% 2.64/1.41  Inference rules
% 2.64/1.41  ----------------------
% 2.64/1.41  #Ref     : 0
% 2.64/1.41  #Sup     : 92
% 2.64/1.41  #Fact    : 0
% 2.64/1.41  #Define  : 0
% 2.64/1.41  #Split   : 1
% 2.64/1.41  #Chain   : 0
% 2.64/1.41  #Close   : 0
% 2.64/1.41  
% 2.64/1.41  Ordering : KBO
% 2.64/1.41  
% 2.64/1.41  Simplification rules
% 2.64/1.41  ----------------------
% 2.64/1.41  #Subsume      : 9
% 2.64/1.41  #Demod        : 27
% 2.64/1.41  #Tautology    : 11
% 2.64/1.41  #SimpNegUnit  : 5
% 2.64/1.41  #BackRed      : 0
% 2.64/1.41  
% 2.64/1.41  #Partial instantiations: 0
% 2.64/1.41  #Strategies tried      : 1
% 2.64/1.41  
% 2.64/1.41  Timing (in seconds)
% 2.64/1.41  ----------------------
% 2.64/1.41  Preprocessing        : 0.29
% 2.64/1.41  Parsing              : 0.17
% 2.64/1.41  CNF conversion       : 0.02
% 2.64/1.41  Main loop            : 0.30
% 2.64/1.41  Inferencing          : 0.12
% 2.64/1.41  Reduction            : 0.07
% 2.64/1.41  Demodulation         : 0.05
% 2.64/1.41  BG Simplification    : 0.02
% 2.64/1.41  Subsumption          : 0.07
% 2.64/1.41  Abstraction          : 0.01
% 2.64/1.41  MUC search           : 0.00
% 2.64/1.41  Cooper               : 0.00
% 2.64/1.41  Total                : 0.62
% 2.64/1.41  Index Insertion      : 0.00
% 2.64/1.41  Index Deletion       : 0.00
% 2.64/1.41  Index Matching       : 0.00
% 2.64/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
