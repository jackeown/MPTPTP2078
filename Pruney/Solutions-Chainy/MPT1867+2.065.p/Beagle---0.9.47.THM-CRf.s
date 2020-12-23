%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:31 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 161 expanded)
%              Number of leaves         :   34 (  70 expanded)
%              Depth                    :   12
%              Number of atoms          :  139 ( 337 expanded)
%              Number of equality atoms :   26 (  57 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_46,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_98,axiom,(
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
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tops_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & v2_tops_1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v1_xboole_0(k1_tops_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_tops_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_38,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_40,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_46,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_44,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_54,plain,(
    ! [A_49] :
      ( k1_xboole_0 = A_49
      | ~ v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_63,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_54])).

tff(c_18,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_73,plain,(
    ! [A_10] : m1_subset_1('#skF_4',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_18])).

tff(c_181,plain,(
    ! [A_80,B_81] :
      ( r1_tarski('#skF_2'(A_80,B_81),B_81)
      | v2_tex_2(B_81,A_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_210,plain,(
    ! [A_84] :
      ( r1_tarski('#skF_2'(A_84,'#skF_4'),'#skF_4')
      | v2_tex_2('#skF_4',A_84)
      | ~ l1_pre_topc(A_84) ) ),
    inference(resolution,[status(thm)],[c_73,c_181])).

tff(c_14,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_65,plain,(
    ! [A_6] : r1_tarski('#skF_4',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_14])).

tff(c_83,plain,(
    ! [B_55,A_56] :
      ( B_55 = A_56
      | ~ r1_tarski(B_55,A_56)
      | ~ r1_tarski(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_91,plain,(
    ! [A_6] :
      ( A_6 = '#skF_4'
      | ~ r1_tarski(A_6,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_65,c_83])).

tff(c_241,plain,(
    ! [A_87] :
      ( '#skF_2'(A_87,'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_87)
      | ~ l1_pre_topc(A_87) ) ),
    inference(resolution,[status(thm)],[c_210,c_91])).

tff(c_244,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_241,c_40])).

tff(c_247,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_244])).

tff(c_48,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_155,plain,(
    ! [B_71,A_72] :
      ( v2_tops_1(B_71,A_72)
      | ~ v1_xboole_0(B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_159,plain,(
    ! [A_72] :
      ( v2_tops_1('#skF_4',A_72)
      | ~ v1_xboole_0('#skF_4')
      | ~ l1_pre_topc(A_72) ) ),
    inference(resolution,[status(thm)],[c_73,c_155])).

tff(c_162,plain,(
    ! [A_72] :
      ( v2_tops_1('#skF_4',A_72)
      | ~ l1_pre_topc(A_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_159])).

tff(c_170,plain,(
    ! [A_77,B_78] :
      ( v1_xboole_0(k1_tops_1(A_77,B_78))
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ v2_tops_1(B_78,A_77)
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_176,plain,(
    ! [A_79] :
      ( v1_xboole_0(k1_tops_1(A_79,'#skF_4'))
      | ~ v2_tops_1('#skF_4',A_79)
      | ~ l1_pre_topc(A_79) ) ),
    inference(resolution,[status(thm)],[c_73,c_170])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_64,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_4])).

tff(c_186,plain,(
    ! [A_82] :
      ( k1_tops_1(A_82,'#skF_4') = '#skF_4'
      | ~ v2_tops_1('#skF_4',A_82)
      | ~ l1_pre_topc(A_82) ) ),
    inference(resolution,[status(thm)],[c_176,c_64])).

tff(c_191,plain,(
    ! [A_83] :
      ( k1_tops_1(A_83,'#skF_4') = '#skF_4'
      | ~ l1_pre_topc(A_83) ) ),
    inference(resolution,[status(thm)],[c_162,c_186])).

tff(c_195,plain,(
    k1_tops_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_191])).

tff(c_164,plain,(
    ! [A_74,B_75] :
      ( v3_pre_topc(k1_tops_1(A_74,B_75),A_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_168,plain,(
    ! [A_74] :
      ( v3_pre_topc(k1_tops_1(A_74,'#skF_4'),A_74)
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74) ) ),
    inference(resolution,[status(thm)],[c_73,c_164])).

tff(c_202,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_168])).

tff(c_208,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_202])).

tff(c_12,plain,(
    ! [A_4,B_5] : r1_tarski(k3_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_96,plain,(
    ! [A_57] :
      ( A_57 = '#skF_4'
      | ~ r1_tarski(A_57,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_65,c_83])).

tff(c_109,plain,(
    ! [B_5] : k3_xboole_0('#skF_4',B_5) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_12,c_96])).

tff(c_142,plain,(
    ! [A_66,B_67,C_68] :
      ( k9_subset_1(A_66,B_67,C_68) = k3_xboole_0(B_67,C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(A_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_145,plain,(
    ! [A_10,B_67] : k9_subset_1(A_10,B_67,'#skF_4') = k3_xboole_0(B_67,'#skF_4') ),
    inference(resolution,[status(thm)],[c_73,c_142])).

tff(c_298,plain,(
    ! [A_97,B_98,D_99] :
      ( k9_subset_1(u1_struct_0(A_97),B_98,D_99) != '#skF_2'(A_97,B_98)
      | ~ v3_pre_topc(D_99,A_97)
      | ~ m1_subset_1(D_99,k1_zfmisc_1(u1_struct_0(A_97)))
      | v2_tex_2(B_98,A_97)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_301,plain,(
    ! [B_67,A_97] :
      ( k3_xboole_0(B_67,'#skF_4') != '#skF_2'(A_97,B_67)
      | ~ v3_pre_topc('#skF_4',A_97)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_97)))
      | v2_tex_2(B_67,A_97)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_298])).

tff(c_317,plain,(
    ! [B_105,A_106] :
      ( k3_xboole_0(B_105,'#skF_4') != '#skF_2'(A_106,B_105)
      | ~ v3_pre_topc('#skF_4',A_106)
      | v2_tex_2(B_105,A_106)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_301])).

tff(c_324,plain,(
    ! [A_106] :
      ( k3_xboole_0('#skF_4','#skF_4') != '#skF_2'(A_106,'#skF_4')
      | ~ v3_pre_topc('#skF_4',A_106)
      | v2_tex_2('#skF_4',A_106)
      | ~ l1_pre_topc(A_106) ) ),
    inference(resolution,[status(thm)],[c_73,c_317])).

tff(c_362,plain,(
    ! [A_110] :
      ( '#skF_2'(A_110,'#skF_4') != '#skF_4'
      | ~ v3_pre_topc('#skF_4',A_110)
      | v2_tex_2('#skF_4',A_110)
      | ~ l1_pre_topc(A_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_324])).

tff(c_365,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_208,c_362])).

tff(c_368,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_247,c_365])).

tff(c_370,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_368])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n019.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 19:44:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.41  
% 2.49/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.41  %$ v3_pre_topc > v2_tops_1 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.49/1.41  
% 2.49/1.41  %Foreground sorts:
% 2.49/1.41  
% 2.49/1.41  
% 2.49/1.41  %Background operators:
% 2.49/1.41  
% 2.49/1.41  
% 2.49/1.41  %Foreground operators:
% 2.49/1.41  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.49/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.49/1.41  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.49/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.49/1.41  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 2.49/1.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.49/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.41  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.49/1.41  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.49/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.49/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.49/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.49/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.49/1.41  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.49/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.49/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.49/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.49/1.41  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.49/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.49/1.41  
% 2.75/1.43  tff(f_113, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 2.75/1.43  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.75/1.43  tff(f_46, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.75/1.43  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 2.75/1.43  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.75/1.43  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.75/1.43  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tops_1)).
% 2.75/1.43  tff(f_69, axiom, (![A, B]: (((l1_pre_topc(A) & v2_tops_1(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v1_xboole_0(k1_tops_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc13_tops_1)).
% 2.75/1.43  tff(f_77, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 2.75/1.43  tff(f_38, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.75/1.43  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.75/1.43  tff(c_40, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.75/1.43  tff(c_46, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.75/1.43  tff(c_44, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.75/1.43  tff(c_54, plain, (![A_49]: (k1_xboole_0=A_49 | ~v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.75/1.43  tff(c_63, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_44, c_54])).
% 2.75/1.43  tff(c_18, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.75/1.43  tff(c_73, plain, (![A_10]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_18])).
% 2.75/1.43  tff(c_181, plain, (![A_80, B_81]: (r1_tarski('#skF_2'(A_80, B_81), B_81) | v2_tex_2(B_81, A_80) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.75/1.43  tff(c_210, plain, (![A_84]: (r1_tarski('#skF_2'(A_84, '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', A_84) | ~l1_pre_topc(A_84))), inference(resolution, [status(thm)], [c_73, c_181])).
% 2.75/1.43  tff(c_14, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.75/1.43  tff(c_65, plain, (![A_6]: (r1_tarski('#skF_4', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_14])).
% 2.75/1.43  tff(c_83, plain, (![B_55, A_56]: (B_55=A_56 | ~r1_tarski(B_55, A_56) | ~r1_tarski(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.75/1.43  tff(c_91, plain, (![A_6]: (A_6='#skF_4' | ~r1_tarski(A_6, '#skF_4'))), inference(resolution, [status(thm)], [c_65, c_83])).
% 2.75/1.43  tff(c_241, plain, (![A_87]: ('#skF_2'(A_87, '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_87) | ~l1_pre_topc(A_87))), inference(resolution, [status(thm)], [c_210, c_91])).
% 2.75/1.43  tff(c_244, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_241, c_40])).
% 2.75/1.43  tff(c_247, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_244])).
% 2.75/1.43  tff(c_48, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.75/1.43  tff(c_155, plain, (![B_71, A_72]: (v2_tops_1(B_71, A_72) | ~v1_xboole_0(B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.75/1.43  tff(c_159, plain, (![A_72]: (v2_tops_1('#skF_4', A_72) | ~v1_xboole_0('#skF_4') | ~l1_pre_topc(A_72))), inference(resolution, [status(thm)], [c_73, c_155])).
% 2.75/1.43  tff(c_162, plain, (![A_72]: (v2_tops_1('#skF_4', A_72) | ~l1_pre_topc(A_72))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_159])).
% 2.75/1.43  tff(c_170, plain, (![A_77, B_78]: (v1_xboole_0(k1_tops_1(A_77, B_78)) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~v2_tops_1(B_78, A_77) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.75/1.43  tff(c_176, plain, (![A_79]: (v1_xboole_0(k1_tops_1(A_79, '#skF_4')) | ~v2_tops_1('#skF_4', A_79) | ~l1_pre_topc(A_79))), inference(resolution, [status(thm)], [c_73, c_170])).
% 2.75/1.43  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.75/1.43  tff(c_64, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_4])).
% 2.75/1.43  tff(c_186, plain, (![A_82]: (k1_tops_1(A_82, '#skF_4')='#skF_4' | ~v2_tops_1('#skF_4', A_82) | ~l1_pre_topc(A_82))), inference(resolution, [status(thm)], [c_176, c_64])).
% 2.75/1.43  tff(c_191, plain, (![A_83]: (k1_tops_1(A_83, '#skF_4')='#skF_4' | ~l1_pre_topc(A_83))), inference(resolution, [status(thm)], [c_162, c_186])).
% 2.75/1.43  tff(c_195, plain, (k1_tops_1('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_46, c_191])).
% 2.75/1.43  tff(c_164, plain, (![A_74, B_75]: (v3_pre_topc(k1_tops_1(A_74, B_75), A_74) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.75/1.43  tff(c_168, plain, (![A_74]: (v3_pre_topc(k1_tops_1(A_74, '#skF_4'), A_74) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74))), inference(resolution, [status(thm)], [c_73, c_164])).
% 2.75/1.43  tff(c_202, plain, (v3_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_195, c_168])).
% 2.75/1.43  tff(c_208, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_202])).
% 2.75/1.43  tff(c_12, plain, (![A_4, B_5]: (r1_tarski(k3_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.75/1.43  tff(c_96, plain, (![A_57]: (A_57='#skF_4' | ~r1_tarski(A_57, '#skF_4'))), inference(resolution, [status(thm)], [c_65, c_83])).
% 2.75/1.43  tff(c_109, plain, (![B_5]: (k3_xboole_0('#skF_4', B_5)='#skF_4')), inference(resolution, [status(thm)], [c_12, c_96])).
% 2.75/1.43  tff(c_142, plain, (![A_66, B_67, C_68]: (k9_subset_1(A_66, B_67, C_68)=k3_xboole_0(B_67, C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.75/1.43  tff(c_145, plain, (![A_10, B_67]: (k9_subset_1(A_10, B_67, '#skF_4')=k3_xboole_0(B_67, '#skF_4'))), inference(resolution, [status(thm)], [c_73, c_142])).
% 2.75/1.43  tff(c_298, plain, (![A_97, B_98, D_99]: (k9_subset_1(u1_struct_0(A_97), B_98, D_99)!='#skF_2'(A_97, B_98) | ~v3_pre_topc(D_99, A_97) | ~m1_subset_1(D_99, k1_zfmisc_1(u1_struct_0(A_97))) | v2_tex_2(B_98, A_97) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.75/1.43  tff(c_301, plain, (![B_67, A_97]: (k3_xboole_0(B_67, '#skF_4')!='#skF_2'(A_97, B_67) | ~v3_pre_topc('#skF_4', A_97) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_97))) | v2_tex_2(B_67, A_97) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(superposition, [status(thm), theory('equality')], [c_145, c_298])).
% 2.75/1.43  tff(c_317, plain, (![B_105, A_106]: (k3_xboole_0(B_105, '#skF_4')!='#skF_2'(A_106, B_105) | ~v3_pre_topc('#skF_4', A_106) | v2_tex_2(B_105, A_106) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_301])).
% 2.75/1.43  tff(c_324, plain, (![A_106]: (k3_xboole_0('#skF_4', '#skF_4')!='#skF_2'(A_106, '#skF_4') | ~v3_pre_topc('#skF_4', A_106) | v2_tex_2('#skF_4', A_106) | ~l1_pre_topc(A_106))), inference(resolution, [status(thm)], [c_73, c_317])).
% 2.75/1.43  tff(c_362, plain, (![A_110]: ('#skF_2'(A_110, '#skF_4')!='#skF_4' | ~v3_pre_topc('#skF_4', A_110) | v2_tex_2('#skF_4', A_110) | ~l1_pre_topc(A_110))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_324])).
% 2.75/1.43  tff(c_365, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_208, c_362])).
% 2.75/1.43  tff(c_368, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_247, c_365])).
% 2.75/1.43  tff(c_370, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_368])).
% 2.75/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.43  
% 2.75/1.43  Inference rules
% 2.75/1.43  ----------------------
% 2.75/1.43  #Ref     : 0
% 2.75/1.43  #Sup     : 67
% 2.75/1.43  #Fact    : 0
% 2.75/1.43  #Define  : 0
% 2.75/1.43  #Split   : 0
% 2.75/1.43  #Chain   : 0
% 2.75/1.43  #Close   : 0
% 2.75/1.43  
% 2.75/1.43  Ordering : KBO
% 2.75/1.43  
% 2.75/1.43  Simplification rules
% 2.75/1.43  ----------------------
% 2.75/1.43  #Subsume      : 3
% 2.75/1.43  #Demod        : 39
% 2.75/1.43  #Tautology    : 25
% 2.75/1.43  #SimpNegUnit  : 6
% 2.75/1.43  #BackRed      : 3
% 2.75/1.43  
% 2.75/1.43  #Partial instantiations: 0
% 2.75/1.43  #Strategies tried      : 1
% 2.75/1.43  
% 2.75/1.43  Timing (in seconds)
% 2.75/1.43  ----------------------
% 2.75/1.43  Preprocessing        : 0.34
% 2.75/1.43  Parsing              : 0.18
% 2.75/1.43  CNF conversion       : 0.02
% 2.75/1.43  Main loop            : 0.25
% 2.75/1.43  Inferencing          : 0.09
% 2.75/1.43  Reduction            : 0.08
% 2.75/1.43  Demodulation         : 0.05
% 2.75/1.43  BG Simplification    : 0.02
% 2.75/1.43  Subsumption          : 0.05
% 2.75/1.43  Abstraction          : 0.02
% 2.75/1.43  MUC search           : 0.00
% 2.75/1.43  Cooper               : 0.00
% 2.75/1.43  Total                : 0.63
% 2.75/1.43  Index Insertion      : 0.00
% 2.75/1.43  Index Deletion       : 0.00
% 2.75/1.43  Index Matching       : 0.00
% 2.75/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
