%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:19 EST 2020

% Result     : Theorem 32.94s
% Output     : CNFRefutation 33.15s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 106 expanded)
%              Number of leaves         :   40 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  143 ( 280 expanded)
%              Number of equality atoms :   19 (  33 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_117,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tex_2(B,A)
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ~ ( r2_hidden(C,B)
                      & ! [D] :
                          ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                         => ~ ( v4_pre_topc(D,A)
                              & k9_subset_1(u1_struct_0(A),B,D) = k1_tarski(C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tex_2)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_62,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( r1_tarski(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v4_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tex_2)).

tff(c_70,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_174,plain,(
    ! [A_108,B_109] :
      ( m1_subset_1(k1_tarski(A_108),k1_zfmisc_1(B_109))
      | ~ r2_hidden(A_108,B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_48,plain,(
    ! [A_42] : ~ v1_xboole_0(k1_zfmisc_1(A_42)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_139,plain,(
    ! [A_100,B_101] :
      ( r2_hidden(A_100,B_101)
      | v1_xboole_0(B_101)
      | ~ m1_subset_1(A_100,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_36,plain,(
    ! [C_41,A_37] :
      ( r1_tarski(C_41,A_37)
      | ~ r2_hidden(C_41,k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_143,plain,(
    ! [A_100,A_37] :
      ( r1_tarski(A_100,A_37)
      | v1_xboole_0(k1_zfmisc_1(A_37))
      | ~ m1_subset_1(A_100,k1_zfmisc_1(A_37)) ) ),
    inference(resolution,[status(thm)],[c_139,c_36])).

tff(c_146,plain,(
    ! [A_100,A_37] :
      ( r1_tarski(A_100,A_37)
      | ~ m1_subset_1(A_100,k1_zfmisc_1(A_37)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_143])).

tff(c_182,plain,(
    ! [A_108,B_109] :
      ( r1_tarski(k1_tarski(A_108),B_109)
      | ~ r2_hidden(A_108,B_109) ) ),
    inference(resolution,[status(thm)],[c_174,c_146])).

tff(c_76,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_156,plain,(
    ! [A_105,A_106] :
      ( r1_tarski(A_105,A_106)
      | ~ m1_subset_1(A_105,k1_zfmisc_1(A_106)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_143])).

tff(c_160,plain,(
    r1_tarski('#skF_8',u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_76,c_156])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_164,plain,(
    k3_xboole_0('#skF_8',u1_struct_0('#skF_7')) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_160,c_20])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_168,plain,(
    ! [D_6] :
      ( r2_hidden(D_6,u1_struct_0('#skF_7'))
      | ~ r2_hidden(D_6,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_4])).

tff(c_78,plain,(
    l1_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_74,plain,(
    v2_tex_2('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_50,plain,(
    ! [A_43,B_44] :
      ( m1_subset_1(k1_tarski(A_43),k1_zfmisc_1(B_44))
      | ~ r2_hidden(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1712,plain,(
    ! [A_288,B_289,C_290] :
      ( v4_pre_topc('#skF_5'(A_288,B_289,C_290),A_288)
      | ~ r1_tarski(C_290,B_289)
      | ~ m1_subset_1(C_290,k1_zfmisc_1(u1_struct_0(A_288)))
      | ~ v2_tex_2(B_289,A_288)
      | ~ m1_subset_1(B_289,k1_zfmisc_1(u1_struct_0(A_288)))
      | ~ l1_pre_topc(A_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1721,plain,(
    ! [A_288,B_289,A_43] :
      ( v4_pre_topc('#skF_5'(A_288,B_289,k1_tarski(A_43)),A_288)
      | ~ r1_tarski(k1_tarski(A_43),B_289)
      | ~ v2_tex_2(B_289,A_288)
      | ~ m1_subset_1(B_289,k1_zfmisc_1(u1_struct_0(A_288)))
      | ~ l1_pre_topc(A_288)
      | ~ r2_hidden(A_43,u1_struct_0(A_288)) ) ),
    inference(resolution,[status(thm)],[c_50,c_1712])).

tff(c_2039,plain,(
    ! [A_322,B_323,C_324] :
      ( k9_subset_1(u1_struct_0(A_322),B_323,'#skF_5'(A_322,B_323,C_324)) = C_324
      | ~ r1_tarski(C_324,B_323)
      | ~ m1_subset_1(C_324,k1_zfmisc_1(u1_struct_0(A_322)))
      | ~ v2_tex_2(B_323,A_322)
      | ~ m1_subset_1(B_323,k1_zfmisc_1(u1_struct_0(A_322)))
      | ~ l1_pre_topc(A_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_18685,plain,(
    ! [A_803,B_804,A_805] :
      ( k9_subset_1(u1_struct_0(A_803),B_804,'#skF_5'(A_803,B_804,k1_tarski(A_805))) = k1_tarski(A_805)
      | ~ r1_tarski(k1_tarski(A_805),B_804)
      | ~ v2_tex_2(B_804,A_803)
      | ~ m1_subset_1(B_804,k1_zfmisc_1(u1_struct_0(A_803)))
      | ~ l1_pre_topc(A_803)
      | ~ r2_hidden(A_805,u1_struct_0(A_803)) ) ),
    inference(resolution,[status(thm)],[c_50,c_2039])).

tff(c_1817,plain,(
    ! [A_296,B_297,C_298] :
      ( m1_subset_1('#skF_5'(A_296,B_297,C_298),k1_zfmisc_1(u1_struct_0(A_296)))
      | ~ r1_tarski(C_298,B_297)
      | ~ m1_subset_1(C_298,k1_zfmisc_1(u1_struct_0(A_296)))
      | ~ v2_tex_2(B_297,A_296)
      | ~ m1_subset_1(B_297,k1_zfmisc_1(u1_struct_0(A_296)))
      | ~ l1_pre_topc(A_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_68,plain,(
    ! [D_85] :
      ( k9_subset_1(u1_struct_0('#skF_7'),'#skF_8',D_85) != k1_tarski('#skF_9')
      | ~ v4_pre_topc(D_85,'#skF_7')
      | ~ m1_subset_1(D_85,k1_zfmisc_1(u1_struct_0('#skF_7'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1836,plain,(
    ! [B_297,C_298] :
      ( k9_subset_1(u1_struct_0('#skF_7'),'#skF_8','#skF_5'('#skF_7',B_297,C_298)) != k1_tarski('#skF_9')
      | ~ v4_pre_topc('#skF_5'('#skF_7',B_297,C_298),'#skF_7')
      | ~ r1_tarski(C_298,B_297)
      | ~ m1_subset_1(C_298,k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ v2_tex_2(B_297,'#skF_7')
      | ~ m1_subset_1(B_297,k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ l1_pre_topc('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1817,c_68])).

tff(c_1848,plain,(
    ! [B_297,C_298] :
      ( k9_subset_1(u1_struct_0('#skF_7'),'#skF_8','#skF_5'('#skF_7',B_297,C_298)) != k1_tarski('#skF_9')
      | ~ v4_pre_topc('#skF_5'('#skF_7',B_297,C_298),'#skF_7')
      | ~ r1_tarski(C_298,B_297)
      | ~ m1_subset_1(C_298,k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ v2_tex_2(B_297,'#skF_7')
      | ~ m1_subset_1(B_297,k1_zfmisc_1(u1_struct_0('#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1836])).

tff(c_18693,plain,(
    ! [A_805] :
      ( k1_tarski(A_805) != k1_tarski('#skF_9')
      | ~ v4_pre_topc('#skF_5'('#skF_7','#skF_8',k1_tarski(A_805)),'#skF_7')
      | ~ r1_tarski(k1_tarski(A_805),'#skF_8')
      | ~ m1_subset_1(k1_tarski(A_805),k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ v2_tex_2('#skF_8','#skF_7')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ r1_tarski(k1_tarski(A_805),'#skF_8')
      | ~ v2_tex_2('#skF_8','#skF_7')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ l1_pre_topc('#skF_7')
      | ~ r2_hidden(A_805,u1_struct_0('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18685,c_1848])).

tff(c_64901,plain,(
    ! [A_1415] :
      ( k1_tarski(A_1415) != k1_tarski('#skF_9')
      | ~ v4_pre_topc('#skF_5'('#skF_7','#skF_8',k1_tarski(A_1415)),'#skF_7')
      | ~ m1_subset_1(k1_tarski(A_1415),k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ r1_tarski(k1_tarski(A_1415),'#skF_8')
      | ~ r2_hidden(A_1415,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_76,c_74,c_18693])).

tff(c_64907,plain,(
    ! [A_1416] :
      ( k1_tarski(A_1416) != k1_tarski('#skF_9')
      | ~ v4_pre_topc('#skF_5'('#skF_7','#skF_8',k1_tarski(A_1416)),'#skF_7')
      | ~ r1_tarski(k1_tarski(A_1416),'#skF_8')
      | ~ r2_hidden(A_1416,u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_50,c_64901])).

tff(c_64911,plain,(
    ! [A_43] :
      ( k1_tarski(A_43) != k1_tarski('#skF_9')
      | ~ r1_tarski(k1_tarski(A_43),'#skF_8')
      | ~ v2_tex_2('#skF_8','#skF_7')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_7')))
      | ~ l1_pre_topc('#skF_7')
      | ~ r2_hidden(A_43,u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_1721,c_64907])).

tff(c_64915,plain,(
    ! [A_1417] :
      ( k1_tarski(A_1417) != k1_tarski('#skF_9')
      | ~ r1_tarski(k1_tarski(A_1417),'#skF_8')
      | ~ r2_hidden(A_1417,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_64911])).

tff(c_65759,plain,(
    ! [D_1418] :
      ( k1_tarski(D_1418) != k1_tarski('#skF_9')
      | ~ r1_tarski(k1_tarski(D_1418),'#skF_8')
      | ~ r2_hidden(D_1418,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_168,c_64915])).

tff(c_65853,plain,(
    ! [A_1421] :
      ( k1_tarski(A_1421) != k1_tarski('#skF_9')
      | ~ r2_hidden(A_1421,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_182,c_65759])).

tff(c_66449,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_70,c_65853])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:05:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 32.94/22.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 33.15/22.51  
% 33.15/22.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 33.15/22.51  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_4
% 33.15/22.51  
% 33.15/22.51  %Foreground sorts:
% 33.15/22.51  
% 33.15/22.51  
% 33.15/22.51  %Background operators:
% 33.15/22.51  
% 33.15/22.51  
% 33.15/22.51  %Foreground operators:
% 33.15/22.51  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 33.15/22.51  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 33.15/22.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 33.15/22.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 33.15/22.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 33.15/22.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 33.15/22.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 33.15/22.51  tff('#skF_7', type, '#skF_7': $i).
% 33.15/22.51  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 33.15/22.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 33.15/22.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 33.15/22.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 33.15/22.51  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 33.15/22.51  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 33.15/22.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 33.15/22.51  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 33.15/22.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 33.15/22.51  tff('#skF_9', type, '#skF_9': $i).
% 33.15/22.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 33.15/22.51  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 33.15/22.51  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 33.15/22.51  tff('#skF_8', type, '#skF_8': $i).
% 33.15/22.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 33.15/22.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 33.15/22.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 33.15/22.51  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 33.15/22.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 33.15/22.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 33.15/22.51  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 33.15/22.51  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 33.15/22.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 33.15/22.51  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 33.15/22.51  
% 33.15/22.53  tff(f_117, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k1_tarski(C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tex_2)).
% 33.15/22.53  tff(f_66, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 33.15/22.53  tff(f_62, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 33.15/22.53  tff(f_74, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 33.15/22.53  tff(f_59, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 33.15/22.53  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 33.15/22.53  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 33.15/22.53  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tex_2)).
% 33.15/22.53  tff(c_70, plain, (r2_hidden('#skF_9', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_117])).
% 33.15/22.53  tff(c_174, plain, (![A_108, B_109]: (m1_subset_1(k1_tarski(A_108), k1_zfmisc_1(B_109)) | ~r2_hidden(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_66])).
% 33.15/22.53  tff(c_48, plain, (![A_42]: (~v1_xboole_0(k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 33.15/22.53  tff(c_139, plain, (![A_100, B_101]: (r2_hidden(A_100, B_101) | v1_xboole_0(B_101) | ~m1_subset_1(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_74])).
% 33.15/22.53  tff(c_36, plain, (![C_41, A_37]: (r1_tarski(C_41, A_37) | ~r2_hidden(C_41, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 33.15/22.53  tff(c_143, plain, (![A_100, A_37]: (r1_tarski(A_100, A_37) | v1_xboole_0(k1_zfmisc_1(A_37)) | ~m1_subset_1(A_100, k1_zfmisc_1(A_37)))), inference(resolution, [status(thm)], [c_139, c_36])).
% 33.15/22.53  tff(c_146, plain, (![A_100, A_37]: (r1_tarski(A_100, A_37) | ~m1_subset_1(A_100, k1_zfmisc_1(A_37)))), inference(negUnitSimplification, [status(thm)], [c_48, c_143])).
% 33.15/22.53  tff(c_182, plain, (![A_108, B_109]: (r1_tarski(k1_tarski(A_108), B_109) | ~r2_hidden(A_108, B_109))), inference(resolution, [status(thm)], [c_174, c_146])).
% 33.15/22.53  tff(c_76, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_7')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 33.15/22.53  tff(c_156, plain, (![A_105, A_106]: (r1_tarski(A_105, A_106) | ~m1_subset_1(A_105, k1_zfmisc_1(A_106)))), inference(negUnitSimplification, [status(thm)], [c_48, c_143])).
% 33.15/22.53  tff(c_160, plain, (r1_tarski('#skF_8', u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_76, c_156])).
% 33.15/22.53  tff(c_20, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 33.15/22.53  tff(c_164, plain, (k3_xboole_0('#skF_8', u1_struct_0('#skF_7'))='#skF_8'), inference(resolution, [status(thm)], [c_160, c_20])).
% 33.15/22.53  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 33.15/22.53  tff(c_168, plain, (![D_6]: (r2_hidden(D_6, u1_struct_0('#skF_7')) | ~r2_hidden(D_6, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_164, c_4])).
% 33.15/22.53  tff(c_78, plain, (l1_pre_topc('#skF_7')), inference(cnfTransformation, [status(thm)], [f_117])).
% 33.15/22.53  tff(c_74, plain, (v2_tex_2('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_117])).
% 33.15/22.53  tff(c_50, plain, (![A_43, B_44]: (m1_subset_1(k1_tarski(A_43), k1_zfmisc_1(B_44)) | ~r2_hidden(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_66])).
% 33.15/22.53  tff(c_1712, plain, (![A_288, B_289, C_290]: (v4_pre_topc('#skF_5'(A_288, B_289, C_290), A_288) | ~r1_tarski(C_290, B_289) | ~m1_subset_1(C_290, k1_zfmisc_1(u1_struct_0(A_288))) | ~v2_tex_2(B_289, A_288) | ~m1_subset_1(B_289, k1_zfmisc_1(u1_struct_0(A_288))) | ~l1_pre_topc(A_288))), inference(cnfTransformation, [status(thm)], [f_95])).
% 33.15/22.53  tff(c_1721, plain, (![A_288, B_289, A_43]: (v4_pre_topc('#skF_5'(A_288, B_289, k1_tarski(A_43)), A_288) | ~r1_tarski(k1_tarski(A_43), B_289) | ~v2_tex_2(B_289, A_288) | ~m1_subset_1(B_289, k1_zfmisc_1(u1_struct_0(A_288))) | ~l1_pre_topc(A_288) | ~r2_hidden(A_43, u1_struct_0(A_288)))), inference(resolution, [status(thm)], [c_50, c_1712])).
% 33.15/22.53  tff(c_2039, plain, (![A_322, B_323, C_324]: (k9_subset_1(u1_struct_0(A_322), B_323, '#skF_5'(A_322, B_323, C_324))=C_324 | ~r1_tarski(C_324, B_323) | ~m1_subset_1(C_324, k1_zfmisc_1(u1_struct_0(A_322))) | ~v2_tex_2(B_323, A_322) | ~m1_subset_1(B_323, k1_zfmisc_1(u1_struct_0(A_322))) | ~l1_pre_topc(A_322))), inference(cnfTransformation, [status(thm)], [f_95])).
% 33.15/22.53  tff(c_18685, plain, (![A_803, B_804, A_805]: (k9_subset_1(u1_struct_0(A_803), B_804, '#skF_5'(A_803, B_804, k1_tarski(A_805)))=k1_tarski(A_805) | ~r1_tarski(k1_tarski(A_805), B_804) | ~v2_tex_2(B_804, A_803) | ~m1_subset_1(B_804, k1_zfmisc_1(u1_struct_0(A_803))) | ~l1_pre_topc(A_803) | ~r2_hidden(A_805, u1_struct_0(A_803)))), inference(resolution, [status(thm)], [c_50, c_2039])).
% 33.15/22.53  tff(c_1817, plain, (![A_296, B_297, C_298]: (m1_subset_1('#skF_5'(A_296, B_297, C_298), k1_zfmisc_1(u1_struct_0(A_296))) | ~r1_tarski(C_298, B_297) | ~m1_subset_1(C_298, k1_zfmisc_1(u1_struct_0(A_296))) | ~v2_tex_2(B_297, A_296) | ~m1_subset_1(B_297, k1_zfmisc_1(u1_struct_0(A_296))) | ~l1_pre_topc(A_296))), inference(cnfTransformation, [status(thm)], [f_95])).
% 33.15/22.53  tff(c_68, plain, (![D_85]: (k9_subset_1(u1_struct_0('#skF_7'), '#skF_8', D_85)!=k1_tarski('#skF_9') | ~v4_pre_topc(D_85, '#skF_7') | ~m1_subset_1(D_85, k1_zfmisc_1(u1_struct_0('#skF_7'))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 33.15/22.53  tff(c_1836, plain, (![B_297, C_298]: (k9_subset_1(u1_struct_0('#skF_7'), '#skF_8', '#skF_5'('#skF_7', B_297, C_298))!=k1_tarski('#skF_9') | ~v4_pre_topc('#skF_5'('#skF_7', B_297, C_298), '#skF_7') | ~r1_tarski(C_298, B_297) | ~m1_subset_1(C_298, k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~v2_tex_2(B_297, '#skF_7') | ~m1_subset_1(B_297, k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~l1_pre_topc('#skF_7'))), inference(resolution, [status(thm)], [c_1817, c_68])).
% 33.15/22.53  tff(c_1848, plain, (![B_297, C_298]: (k9_subset_1(u1_struct_0('#skF_7'), '#skF_8', '#skF_5'('#skF_7', B_297, C_298))!=k1_tarski('#skF_9') | ~v4_pre_topc('#skF_5'('#skF_7', B_297, C_298), '#skF_7') | ~r1_tarski(C_298, B_297) | ~m1_subset_1(C_298, k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~v2_tex_2(B_297, '#skF_7') | ~m1_subset_1(B_297, k1_zfmisc_1(u1_struct_0('#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1836])).
% 33.15/22.53  tff(c_18693, plain, (![A_805]: (k1_tarski(A_805)!=k1_tarski('#skF_9') | ~v4_pre_topc('#skF_5'('#skF_7', '#skF_8', k1_tarski(A_805)), '#skF_7') | ~r1_tarski(k1_tarski(A_805), '#skF_8') | ~m1_subset_1(k1_tarski(A_805), k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~v2_tex_2('#skF_8', '#skF_7') | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~r1_tarski(k1_tarski(A_805), '#skF_8') | ~v2_tex_2('#skF_8', '#skF_7') | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~l1_pre_topc('#skF_7') | ~r2_hidden(A_805, u1_struct_0('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_18685, c_1848])).
% 33.15/22.53  tff(c_64901, plain, (![A_1415]: (k1_tarski(A_1415)!=k1_tarski('#skF_9') | ~v4_pre_topc('#skF_5'('#skF_7', '#skF_8', k1_tarski(A_1415)), '#skF_7') | ~m1_subset_1(k1_tarski(A_1415), k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~r1_tarski(k1_tarski(A_1415), '#skF_8') | ~r2_hidden(A_1415, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_76, c_74, c_18693])).
% 33.15/22.53  tff(c_64907, plain, (![A_1416]: (k1_tarski(A_1416)!=k1_tarski('#skF_9') | ~v4_pre_topc('#skF_5'('#skF_7', '#skF_8', k1_tarski(A_1416)), '#skF_7') | ~r1_tarski(k1_tarski(A_1416), '#skF_8') | ~r2_hidden(A_1416, u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_50, c_64901])).
% 33.15/22.53  tff(c_64911, plain, (![A_43]: (k1_tarski(A_43)!=k1_tarski('#skF_9') | ~r1_tarski(k1_tarski(A_43), '#skF_8') | ~v2_tex_2('#skF_8', '#skF_7') | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_7'))) | ~l1_pre_topc('#skF_7') | ~r2_hidden(A_43, u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_1721, c_64907])).
% 33.15/22.53  tff(c_64915, plain, (![A_1417]: (k1_tarski(A_1417)!=k1_tarski('#skF_9') | ~r1_tarski(k1_tarski(A_1417), '#skF_8') | ~r2_hidden(A_1417, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_64911])).
% 33.15/22.53  tff(c_65759, plain, (![D_1418]: (k1_tarski(D_1418)!=k1_tarski('#skF_9') | ~r1_tarski(k1_tarski(D_1418), '#skF_8') | ~r2_hidden(D_1418, '#skF_8'))), inference(resolution, [status(thm)], [c_168, c_64915])).
% 33.15/22.53  tff(c_65853, plain, (![A_1421]: (k1_tarski(A_1421)!=k1_tarski('#skF_9') | ~r2_hidden(A_1421, '#skF_8'))), inference(resolution, [status(thm)], [c_182, c_65759])).
% 33.15/22.53  tff(c_66449, plain, $false, inference(resolution, [status(thm)], [c_70, c_65853])).
% 33.15/22.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 33.15/22.53  
% 33.15/22.53  Inference rules
% 33.15/22.53  ----------------------
% 33.15/22.53  #Ref     : 0
% 33.15/22.53  #Sup     : 17570
% 33.15/22.53  #Fact    : 0
% 33.15/22.53  #Define  : 0
% 33.15/22.53  #Split   : 8
% 33.15/22.53  #Chain   : 0
% 33.15/22.53  #Close   : 0
% 33.15/22.53  
% 33.15/22.53  Ordering : KBO
% 33.15/22.53  
% 33.15/22.53  Simplification rules
% 33.15/22.53  ----------------------
% 33.15/22.53  #Subsume      : 1070
% 33.15/22.53  #Demod        : 1478
% 33.15/22.53  #Tautology    : 455
% 33.15/22.53  #SimpNegUnit  : 28
% 33.15/22.53  #BackRed      : 6
% 33.15/22.53  
% 33.15/22.53  #Partial instantiations: 0
% 33.15/22.53  #Strategies tried      : 1
% 33.15/22.53  
% 33.15/22.53  Timing (in seconds)
% 33.15/22.53  ----------------------
% 33.15/22.53  Preprocessing        : 0.37
% 33.15/22.53  Parsing              : 0.18
% 33.15/22.53  CNF conversion       : 0.03
% 33.15/22.53  Main loop            : 21.34
% 33.15/22.53  Inferencing          : 2.94
% 33.15/22.53  Reduction            : 2.98
% 33.15/22.53  Demodulation         : 2.07
% 33.15/22.53  BG Simplification    : 0.65
% 33.15/22.53  Subsumption          : 13.56
% 33.15/22.53  Abstraction          : 1.09
% 33.15/22.53  MUC search           : 0.00
% 33.15/22.53  Cooper               : 0.00
% 33.15/22.53  Total                : 21.78
% 33.15/22.53  Index Insertion      : 0.00
% 33.15/22.53  Index Deletion       : 0.00
% 33.15/22.53  Index Matching       : 0.00
% 33.15/22.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
