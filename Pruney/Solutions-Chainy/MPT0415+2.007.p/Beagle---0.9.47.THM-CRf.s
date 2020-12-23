%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:46 EST 2020

% Result     : Theorem 43.65s
% Output     : CNFRefutation 43.65s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 193 expanded)
%              Number of leaves         :   29 (  76 expanded)
%              Depth                    :   20
%              Number of atoms          :  165 ( 376 expanded)
%              Number of equality atoms :   22 (  83 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ~ ( B != k1_xboole_0
            & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

tff(f_47,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_97,plain,(
    ! [A_48,B_49] :
      ( ~ r2_hidden('#skF_1'(A_48,B_49),B_49)
      | r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_106,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_97])).

tff(c_108,plain,(
    ! [C_50,B_51,A_52] :
      ( r2_hidden(C_50,B_51)
      | ~ r2_hidden(C_50,A_52)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_113,plain,(
    ! [A_1,B_2,B_51] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_51)
      | ~ r1_tarski(A_1,B_51)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_108])).

tff(c_52,plain,(
    k7_setfam_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_174,plain,(
    ! [A_69,B_70] :
      ( k7_setfam_1(A_69,k7_setfam_1(A_69,B_70)) = B_70
      | ~ m1_subset_1(B_70,k1_zfmisc_1(k1_zfmisc_1(A_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_179,plain,(
    k7_setfam_1('#skF_5',k7_setfam_1('#skF_5','#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_56,c_174])).

tff(c_185,plain,(
    k7_setfam_1('#skF_5',k1_xboole_0) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_179])).

tff(c_26,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_261,plain,(
    ! [A_83,B_84] :
      ( m1_subset_1(k7_setfam_1(A_83,B_84),k1_zfmisc_1(k1_zfmisc_1(A_83)))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(k1_zfmisc_1(A_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_50,plain,(
    ! [A_31,C_33,B_32] :
      ( m1_subset_1(A_31,C_33)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(C_33))
      | ~ r2_hidden(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2131,plain,(
    ! [A_194,A_195,B_196] :
      ( m1_subset_1(A_194,k1_zfmisc_1(A_195))
      | ~ r2_hidden(A_194,k7_setfam_1(A_195,B_196))
      | ~ m1_subset_1(B_196,k1_zfmisc_1(k1_zfmisc_1(A_195))) ) ),
    inference(resolution,[status(thm)],[c_261,c_50])).

tff(c_60780,plain,(
    ! [A_1182,B_1183,A_1184,B_1185] :
      ( m1_subset_1('#skF_1'(A_1182,B_1183),k1_zfmisc_1(A_1184))
      | ~ m1_subset_1(B_1185,k1_zfmisc_1(k1_zfmisc_1(A_1184)))
      | ~ r1_tarski(A_1182,k7_setfam_1(A_1184,B_1185))
      | r1_tarski(A_1182,B_1183) ) ),
    inference(resolution,[status(thm)],[c_113,c_2131])).

tff(c_60846,plain,(
    ! [A_1182,B_1183,A_1184] :
      ( m1_subset_1('#skF_1'(A_1182,B_1183),k1_zfmisc_1(A_1184))
      | ~ r1_tarski(A_1182,k7_setfam_1(A_1184,k1_xboole_0))
      | r1_tarski(A_1182,B_1183) ) ),
    inference(resolution,[status(thm)],[c_26,c_60780])).

tff(c_91,plain,(
    ! [A_46,B_47] :
      ( r2_hidden('#skF_1'(A_46,B_47),A_46)
      | r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [C_11,A_7] :
      ( r1_tarski(C_11,A_7)
      | ~ r2_hidden(C_11,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_231,plain,(
    ! [A_80,B_81] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(A_80),B_81),A_80)
      | r1_tarski(k1_zfmisc_1(A_80),B_81) ) ),
    inference(resolution,[status(thm)],[c_91,c_12])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_247,plain,(
    ! [B_82] :
      ( '#skF_1'(k1_zfmisc_1(k1_xboole_0),B_82) = k1_xboole_0
      | r1_tarski(k1_zfmisc_1(k1_xboole_0),B_82) ) ),
    inference(resolution,[status(thm)],[c_231,c_10])).

tff(c_259,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | '#skF_1'(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_247,c_10])).

tff(c_260,plain,(
    '#skF_1'(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_259])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_295,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_xboole_0)
    | r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_4])).

tff(c_303,plain,(
    ~ r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_295])).

tff(c_122,plain,(
    ! [A_54,C_55,B_56] :
      ( m1_subset_1(A_54,C_55)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(C_55))
      | ~ r2_hidden(A_54,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_130,plain,(
    ! [A_54] :
      ( m1_subset_1(A_54,k1_zfmisc_1('#skF_5'))
      | ~ r2_hidden(A_54,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_56,c_122])).

tff(c_64,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,B_38)
      | ~ m1_subset_1(A_37,k1_zfmisc_1(B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_72,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(resolution,[status(thm)],[c_26,c_64])).

tff(c_1279,plain,(
    ! [A_143,D_144,B_145] :
      ( r2_hidden(k3_subset_1(A_143,D_144),B_145)
      | ~ r2_hidden(D_144,k7_setfam_1(A_143,B_145))
      | ~ m1_subset_1(D_144,k1_zfmisc_1(A_143))
      | ~ m1_subset_1(k7_setfam_1(A_143,B_145),k1_zfmisc_1(k1_zfmisc_1(A_143)))
      | ~ m1_subset_1(B_145,k1_zfmisc_1(k1_zfmisc_1(A_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1291,plain,(
    ! [D_144] :
      ( r2_hidden(k3_subset_1('#skF_5',D_144),k1_xboole_0)
      | ~ r2_hidden(D_144,k7_setfam_1('#skF_5',k1_xboole_0))
      | ~ m1_subset_1(D_144,k1_zfmisc_1('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1('#skF_5')))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_1279])).

tff(c_1507,plain,(
    ! [D_163] :
      ( r2_hidden(k3_subset_1('#skF_5',D_163),k1_xboole_0)
      | ~ r2_hidden(D_163,'#skF_6')
      | ~ m1_subset_1(D_163,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_56,c_185,c_1291])).

tff(c_48,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(A_29,k1_zfmisc_1(B_30))
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_129,plain,(
    ! [A_54,B_30,A_29] :
      ( m1_subset_1(A_54,B_30)
      | ~ r2_hidden(A_54,A_29)
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(resolution,[status(thm)],[c_48,c_122])).

tff(c_1513,plain,(
    ! [D_163,B_30] :
      ( m1_subset_1(k3_subset_1('#skF_5',D_163),B_30)
      | ~ r1_tarski(k1_xboole_0,B_30)
      | ~ r2_hidden(D_163,'#skF_6')
      | ~ m1_subset_1(D_163,k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1507,c_129])).

tff(c_1617,plain,(
    ! [D_169,B_170] :
      ( m1_subset_1(k3_subset_1('#skF_5',D_169),B_170)
      | ~ r2_hidden(D_169,'#skF_6')
      | ~ m1_subset_1(D_169,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1513])).

tff(c_46,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(A_29,B_30)
      | ~ m1_subset_1(A_29,k1_zfmisc_1(B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1704,plain,(
    ! [D_176,B_177] :
      ( r1_tarski(k3_subset_1('#skF_5',D_176),B_177)
      | ~ r2_hidden(D_176,'#skF_6')
      | ~ m1_subset_1(D_176,k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1617,c_46])).

tff(c_1732,plain,(
    ! [D_178] :
      ( k3_subset_1('#skF_5',D_178) = k1_xboole_0
      | ~ r2_hidden(D_178,'#skF_6')
      | ~ m1_subset_1(D_178,k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1704,c_10])).

tff(c_1767,plain,(
    ! [A_179] :
      ( k3_subset_1('#skF_5',A_179) = k1_xboole_0
      | ~ r2_hidden(A_179,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_130,c_1732])).

tff(c_1809,plain,(
    ! [B_2] :
      ( k3_subset_1('#skF_5','#skF_1'('#skF_6',B_2)) = k1_xboole_0
      | r1_tarski('#skF_6',B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_1767])).

tff(c_42,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1(k7_setfam_1(A_25,B_26),k1_zfmisc_1(k1_zfmisc_1(A_25)))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(k1_zfmisc_1(A_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3881,plain,(
    ! [A_261,D_262,B_263] :
      ( r2_hidden(k3_subset_1(A_261,D_262),B_263)
      | ~ r2_hidden(D_262,k7_setfam_1(A_261,B_263))
      | ~ m1_subset_1(D_262,k1_zfmisc_1(A_261))
      | ~ m1_subset_1(B_263,k1_zfmisc_1(k1_zfmisc_1(A_261))) ) ),
    inference(resolution,[status(thm)],[c_42,c_1279])).

tff(c_6466,plain,(
    ! [A_348,D_349] :
      ( r2_hidden(k3_subset_1(A_348,D_349),k1_xboole_0)
      | ~ r2_hidden(D_349,k7_setfam_1(A_348,k1_xboole_0))
      | ~ m1_subset_1(D_349,k1_zfmisc_1(A_348)) ) ),
    inference(resolution,[status(thm)],[c_26,c_3881])).

tff(c_6498,plain,(
    ! [B_2] :
      ( r2_hidden(k1_xboole_0,k1_xboole_0)
      | ~ r2_hidden('#skF_1'('#skF_6',B_2),k7_setfam_1('#skF_5',k1_xboole_0))
      | ~ m1_subset_1('#skF_1'('#skF_6',B_2),k1_zfmisc_1('#skF_5'))
      | r1_tarski('#skF_6',B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1809,c_6466])).

tff(c_6528,plain,(
    ! [B_2] :
      ( r2_hidden(k1_xboole_0,k1_xboole_0)
      | ~ r2_hidden('#skF_1'('#skF_6',B_2),'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_2),k1_zfmisc_1('#skF_5'))
      | r1_tarski('#skF_6',B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_6498])).

tff(c_112708,plain,(
    ! [B_1847] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_1847),'#skF_6')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_1847),k1_zfmisc_1('#skF_5'))
      | r1_tarski('#skF_6',B_1847) ) ),
    inference(negUnitSimplification,[status(thm)],[c_303,c_6528])).

tff(c_112716,plain,(
    ! [B_1183] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_1183),'#skF_6')
      | ~ r1_tarski('#skF_6',k7_setfam_1('#skF_5',k1_xboole_0))
      | r1_tarski('#skF_6',B_1183) ) ),
    inference(resolution,[status(thm)],[c_60846,c_112708])).

tff(c_113214,plain,(
    ! [B_1853] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_1853),'#skF_6')
      | r1_tarski('#skF_6',B_1853) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_185,c_112716])).

tff(c_113231,plain,(
    ! [B_2] :
      ( ~ r1_tarski('#skF_6','#skF_6')
      | r1_tarski('#skF_6',B_2) ) ),
    inference(resolution,[status(thm)],[c_113,c_113214])).

tff(c_113260,plain,(
    ! [B_1854] : r1_tarski('#skF_6',B_1854) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_113231])).

tff(c_113520,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_113260,c_10])).

tff(c_113660,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_113520])).

tff(c_113661,plain,(
    r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_295])).

tff(c_113812,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_113661,c_10])).

tff(c_24,plain,(
    ! [A_12] : ~ v1_xboole_0(k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_113854,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_113812,c_24])).

tff(c_113868,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_113854])).

tff(c_113869,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_259])).

tff(c_113908,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_113869,c_24])).

tff(c_113919,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_113908])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:22:10 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 43.65/33.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.65/33.63  
% 43.65/33.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.65/33.63  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 43.65/33.63  
% 43.65/33.63  %Foreground sorts:
% 43.65/33.63  
% 43.65/33.63  
% 43.65/33.63  %Background operators:
% 43.65/33.63  
% 43.65/33.63  
% 43.65/33.63  %Foreground operators:
% 43.65/33.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 43.65/33.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 43.65/33.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 43.65/33.63  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 43.65/33.63  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 43.65/33.63  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 43.65/33.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 43.65/33.63  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 43.65/33.63  tff('#skF_5', type, '#skF_5': $i).
% 43.65/33.63  tff('#skF_6', type, '#skF_6': $i).
% 43.65/33.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 43.65/33.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 43.65/33.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 43.65/33.63  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 43.65/33.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 43.65/33.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 43.65/33.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 43.65/33.63  
% 43.65/33.65  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 43.65/33.65  tff(f_90, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_setfam_1)).
% 43.65/33.65  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 43.65/33.65  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 43.65/33.65  tff(f_49, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 43.65/33.65  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 43.65/33.65  tff(f_81, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 43.65/33.65  tff(f_44, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 43.65/33.65  tff(f_37, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 43.65/33.65  tff(f_75, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 43.65/33.65  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_setfam_1)).
% 43.65/33.65  tff(f_47, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 43.65/33.65  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 43.65/33.65  tff(c_54, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_90])).
% 43.65/33.65  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 43.65/33.65  tff(c_97, plain, (![A_48, B_49]: (~r2_hidden('#skF_1'(A_48, B_49), B_49) | r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_32])).
% 43.65/33.65  tff(c_106, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_97])).
% 43.65/33.65  tff(c_108, plain, (![C_50, B_51, A_52]: (r2_hidden(C_50, B_51) | ~r2_hidden(C_50, A_52) | ~r1_tarski(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_32])).
% 43.65/33.65  tff(c_113, plain, (![A_1, B_2, B_51]: (r2_hidden('#skF_1'(A_1, B_2), B_51) | ~r1_tarski(A_1, B_51) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_108])).
% 43.65/33.65  tff(c_52, plain, (k7_setfam_1('#skF_5', '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 43.65/33.65  tff(c_56, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 43.65/33.65  tff(c_174, plain, (![A_69, B_70]: (k7_setfam_1(A_69, k7_setfam_1(A_69, B_70))=B_70 | ~m1_subset_1(B_70, k1_zfmisc_1(k1_zfmisc_1(A_69))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 43.65/33.65  tff(c_179, plain, (k7_setfam_1('#skF_5', k7_setfam_1('#skF_5', '#skF_6'))='#skF_6'), inference(resolution, [status(thm)], [c_56, c_174])).
% 43.65/33.65  tff(c_185, plain, (k7_setfam_1('#skF_5', k1_xboole_0)='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_179])).
% 43.65/33.65  tff(c_26, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 43.65/33.65  tff(c_261, plain, (![A_83, B_84]: (m1_subset_1(k7_setfam_1(A_83, B_84), k1_zfmisc_1(k1_zfmisc_1(A_83))) | ~m1_subset_1(B_84, k1_zfmisc_1(k1_zfmisc_1(A_83))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 43.65/33.65  tff(c_50, plain, (![A_31, C_33, B_32]: (m1_subset_1(A_31, C_33) | ~m1_subset_1(B_32, k1_zfmisc_1(C_33)) | ~r2_hidden(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_81])).
% 43.65/33.65  tff(c_2131, plain, (![A_194, A_195, B_196]: (m1_subset_1(A_194, k1_zfmisc_1(A_195)) | ~r2_hidden(A_194, k7_setfam_1(A_195, B_196)) | ~m1_subset_1(B_196, k1_zfmisc_1(k1_zfmisc_1(A_195))))), inference(resolution, [status(thm)], [c_261, c_50])).
% 43.65/33.65  tff(c_60780, plain, (![A_1182, B_1183, A_1184, B_1185]: (m1_subset_1('#skF_1'(A_1182, B_1183), k1_zfmisc_1(A_1184)) | ~m1_subset_1(B_1185, k1_zfmisc_1(k1_zfmisc_1(A_1184))) | ~r1_tarski(A_1182, k7_setfam_1(A_1184, B_1185)) | r1_tarski(A_1182, B_1183))), inference(resolution, [status(thm)], [c_113, c_2131])).
% 43.65/33.65  tff(c_60846, plain, (![A_1182, B_1183, A_1184]: (m1_subset_1('#skF_1'(A_1182, B_1183), k1_zfmisc_1(A_1184)) | ~r1_tarski(A_1182, k7_setfam_1(A_1184, k1_xboole_0)) | r1_tarski(A_1182, B_1183))), inference(resolution, [status(thm)], [c_26, c_60780])).
% 43.65/33.65  tff(c_91, plain, (![A_46, B_47]: (r2_hidden('#skF_1'(A_46, B_47), A_46) | r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_32])).
% 43.65/33.65  tff(c_12, plain, (![C_11, A_7]: (r1_tarski(C_11, A_7) | ~r2_hidden(C_11, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 43.65/33.65  tff(c_231, plain, (![A_80, B_81]: (r1_tarski('#skF_1'(k1_zfmisc_1(A_80), B_81), A_80) | r1_tarski(k1_zfmisc_1(A_80), B_81))), inference(resolution, [status(thm)], [c_91, c_12])).
% 43.65/33.65  tff(c_10, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 43.65/33.65  tff(c_247, plain, (![B_82]: ('#skF_1'(k1_zfmisc_1(k1_xboole_0), B_82)=k1_xboole_0 | r1_tarski(k1_zfmisc_1(k1_xboole_0), B_82))), inference(resolution, [status(thm)], [c_231, c_10])).
% 43.65/33.65  tff(c_259, plain, (k1_zfmisc_1(k1_xboole_0)=k1_xboole_0 | '#skF_1'(k1_zfmisc_1(k1_xboole_0), k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_247, c_10])).
% 43.65/33.65  tff(c_260, plain, ('#skF_1'(k1_zfmisc_1(k1_xboole_0), k1_xboole_0)=k1_xboole_0), inference(splitLeft, [status(thm)], [c_259])).
% 43.65/33.65  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 43.65/33.65  tff(c_295, plain, (~r2_hidden(k1_xboole_0, k1_xboole_0) | r1_tarski(k1_zfmisc_1(k1_xboole_0), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_260, c_4])).
% 43.65/33.65  tff(c_303, plain, (~r2_hidden(k1_xboole_0, k1_xboole_0)), inference(splitLeft, [status(thm)], [c_295])).
% 43.65/33.65  tff(c_122, plain, (![A_54, C_55, B_56]: (m1_subset_1(A_54, C_55) | ~m1_subset_1(B_56, k1_zfmisc_1(C_55)) | ~r2_hidden(A_54, B_56))), inference(cnfTransformation, [status(thm)], [f_81])).
% 43.65/33.65  tff(c_130, plain, (![A_54]: (m1_subset_1(A_54, k1_zfmisc_1('#skF_5')) | ~r2_hidden(A_54, '#skF_6'))), inference(resolution, [status(thm)], [c_56, c_122])).
% 43.65/33.65  tff(c_64, plain, (![A_37, B_38]: (r1_tarski(A_37, B_38) | ~m1_subset_1(A_37, k1_zfmisc_1(B_38)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 43.65/33.65  tff(c_72, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(resolution, [status(thm)], [c_26, c_64])).
% 43.65/33.65  tff(c_1279, plain, (![A_143, D_144, B_145]: (r2_hidden(k3_subset_1(A_143, D_144), B_145) | ~r2_hidden(D_144, k7_setfam_1(A_143, B_145)) | ~m1_subset_1(D_144, k1_zfmisc_1(A_143)) | ~m1_subset_1(k7_setfam_1(A_143, B_145), k1_zfmisc_1(k1_zfmisc_1(A_143))) | ~m1_subset_1(B_145, k1_zfmisc_1(k1_zfmisc_1(A_143))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 43.65/33.65  tff(c_1291, plain, (![D_144]: (r2_hidden(k3_subset_1('#skF_5', D_144), k1_xboole_0) | ~r2_hidden(D_144, k7_setfam_1('#skF_5', k1_xboole_0)) | ~m1_subset_1(D_144, k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1('#skF_5'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_185, c_1279])).
% 43.65/33.65  tff(c_1507, plain, (![D_163]: (r2_hidden(k3_subset_1('#skF_5', D_163), k1_xboole_0) | ~r2_hidden(D_163, '#skF_6') | ~m1_subset_1(D_163, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_56, c_185, c_1291])).
% 43.65/33.65  tff(c_48, plain, (![A_29, B_30]: (m1_subset_1(A_29, k1_zfmisc_1(B_30)) | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_75])).
% 43.65/33.65  tff(c_129, plain, (![A_54, B_30, A_29]: (m1_subset_1(A_54, B_30) | ~r2_hidden(A_54, A_29) | ~r1_tarski(A_29, B_30))), inference(resolution, [status(thm)], [c_48, c_122])).
% 43.65/33.65  tff(c_1513, plain, (![D_163, B_30]: (m1_subset_1(k3_subset_1('#skF_5', D_163), B_30) | ~r1_tarski(k1_xboole_0, B_30) | ~r2_hidden(D_163, '#skF_6') | ~m1_subset_1(D_163, k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_1507, c_129])).
% 43.65/33.65  tff(c_1617, plain, (![D_169, B_170]: (m1_subset_1(k3_subset_1('#skF_5', D_169), B_170) | ~r2_hidden(D_169, '#skF_6') | ~m1_subset_1(D_169, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1513])).
% 43.65/33.65  tff(c_46, plain, (![A_29, B_30]: (r1_tarski(A_29, B_30) | ~m1_subset_1(A_29, k1_zfmisc_1(B_30)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 43.65/33.65  tff(c_1704, plain, (![D_176, B_177]: (r1_tarski(k3_subset_1('#skF_5', D_176), B_177) | ~r2_hidden(D_176, '#skF_6') | ~m1_subset_1(D_176, k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_1617, c_46])).
% 43.65/33.65  tff(c_1732, plain, (![D_178]: (k3_subset_1('#skF_5', D_178)=k1_xboole_0 | ~r2_hidden(D_178, '#skF_6') | ~m1_subset_1(D_178, k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_1704, c_10])).
% 43.65/33.65  tff(c_1767, plain, (![A_179]: (k3_subset_1('#skF_5', A_179)=k1_xboole_0 | ~r2_hidden(A_179, '#skF_6'))), inference(resolution, [status(thm)], [c_130, c_1732])).
% 43.65/33.65  tff(c_1809, plain, (![B_2]: (k3_subset_1('#skF_5', '#skF_1'('#skF_6', B_2))=k1_xboole_0 | r1_tarski('#skF_6', B_2))), inference(resolution, [status(thm)], [c_6, c_1767])).
% 43.65/33.65  tff(c_42, plain, (![A_25, B_26]: (m1_subset_1(k7_setfam_1(A_25, B_26), k1_zfmisc_1(k1_zfmisc_1(A_25))) | ~m1_subset_1(B_26, k1_zfmisc_1(k1_zfmisc_1(A_25))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 43.65/33.65  tff(c_3881, plain, (![A_261, D_262, B_263]: (r2_hidden(k3_subset_1(A_261, D_262), B_263) | ~r2_hidden(D_262, k7_setfam_1(A_261, B_263)) | ~m1_subset_1(D_262, k1_zfmisc_1(A_261)) | ~m1_subset_1(B_263, k1_zfmisc_1(k1_zfmisc_1(A_261))))), inference(resolution, [status(thm)], [c_42, c_1279])).
% 43.65/33.65  tff(c_6466, plain, (![A_348, D_349]: (r2_hidden(k3_subset_1(A_348, D_349), k1_xboole_0) | ~r2_hidden(D_349, k7_setfam_1(A_348, k1_xboole_0)) | ~m1_subset_1(D_349, k1_zfmisc_1(A_348)))), inference(resolution, [status(thm)], [c_26, c_3881])).
% 43.65/33.65  tff(c_6498, plain, (![B_2]: (r2_hidden(k1_xboole_0, k1_xboole_0) | ~r2_hidden('#skF_1'('#skF_6', B_2), k7_setfam_1('#skF_5', k1_xboole_0)) | ~m1_subset_1('#skF_1'('#skF_6', B_2), k1_zfmisc_1('#skF_5')) | r1_tarski('#skF_6', B_2))), inference(superposition, [status(thm), theory('equality')], [c_1809, c_6466])).
% 43.65/33.65  tff(c_6528, plain, (![B_2]: (r2_hidden(k1_xboole_0, k1_xboole_0) | ~r2_hidden('#skF_1'('#skF_6', B_2), '#skF_6') | ~m1_subset_1('#skF_1'('#skF_6', B_2), k1_zfmisc_1('#skF_5')) | r1_tarski('#skF_6', B_2))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_6498])).
% 43.65/33.65  tff(c_112708, plain, (![B_1847]: (~r2_hidden('#skF_1'('#skF_6', B_1847), '#skF_6') | ~m1_subset_1('#skF_1'('#skF_6', B_1847), k1_zfmisc_1('#skF_5')) | r1_tarski('#skF_6', B_1847))), inference(negUnitSimplification, [status(thm)], [c_303, c_6528])).
% 43.65/33.65  tff(c_112716, plain, (![B_1183]: (~r2_hidden('#skF_1'('#skF_6', B_1183), '#skF_6') | ~r1_tarski('#skF_6', k7_setfam_1('#skF_5', k1_xboole_0)) | r1_tarski('#skF_6', B_1183))), inference(resolution, [status(thm)], [c_60846, c_112708])).
% 43.65/33.65  tff(c_113214, plain, (![B_1853]: (~r2_hidden('#skF_1'('#skF_6', B_1853), '#skF_6') | r1_tarski('#skF_6', B_1853))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_185, c_112716])).
% 43.65/33.65  tff(c_113231, plain, (![B_2]: (~r1_tarski('#skF_6', '#skF_6') | r1_tarski('#skF_6', B_2))), inference(resolution, [status(thm)], [c_113, c_113214])).
% 43.65/33.65  tff(c_113260, plain, (![B_1854]: (r1_tarski('#skF_6', B_1854))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_113231])).
% 43.65/33.65  tff(c_113520, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_113260, c_10])).
% 43.65/33.65  tff(c_113660, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_113520])).
% 43.65/33.65  tff(c_113661, plain, (r1_tarski(k1_zfmisc_1(k1_xboole_0), k1_xboole_0)), inference(splitRight, [status(thm)], [c_295])).
% 43.65/33.65  tff(c_113812, plain, (k1_zfmisc_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_113661, c_10])).
% 43.65/33.65  tff(c_24, plain, (![A_12]: (~v1_xboole_0(k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 43.65/33.65  tff(c_113854, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_113812, c_24])).
% 43.65/33.65  tff(c_113868, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_113854])).
% 43.65/33.65  tff(c_113869, plain, (k1_zfmisc_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_259])).
% 43.65/33.65  tff(c_113908, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_113869, c_24])).
% 43.65/33.65  tff(c_113919, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_113908])).
% 43.65/33.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 43.65/33.65  
% 43.65/33.65  Inference rules
% 43.65/33.65  ----------------------
% 43.65/33.65  #Ref     : 0
% 43.65/33.65  #Sup     : 27860
% 43.65/33.65  #Fact    : 4
% 43.65/33.65  #Define  : 0
% 43.65/33.65  #Split   : 157
% 43.65/33.65  #Chain   : 0
% 43.65/33.65  #Close   : 0
% 43.65/33.65  
% 43.65/33.65  Ordering : KBO
% 43.65/33.65  
% 43.65/33.65  Simplification rules
% 43.65/33.65  ----------------------
% 43.65/33.65  #Subsume      : 6371
% 43.65/33.65  #Demod        : 9133
% 43.65/33.65  #Tautology    : 3994
% 43.65/33.65  #SimpNegUnit  : 1096
% 43.65/33.65  #BackRed      : 405
% 43.65/33.65  
% 43.65/33.65  #Partial instantiations: 0
% 43.65/33.65  #Strategies tried      : 1
% 43.65/33.65  
% 43.65/33.65  Timing (in seconds)
% 43.65/33.65  ----------------------
% 43.65/33.65  Preprocessing        : 0.33
% 43.65/33.65  Parsing              : 0.17
% 43.65/33.65  CNF conversion       : 0.03
% 43.65/33.65  Main loop            : 32.46
% 43.65/33.65  Inferencing          : 3.28
% 43.65/33.65  Reduction            : 7.49
% 43.65/33.65  Demodulation         : 5.00
% 43.65/33.65  BG Simplification    : 0.45
% 43.65/33.65  Subsumption          : 19.59
% 43.65/33.65  Abstraction          : 0.66
% 43.65/33.65  MUC search           : 0.00
% 43.65/33.65  Cooper               : 0.00
% 43.65/33.65  Total                : 32.82
% 43.65/33.65  Index Insertion      : 0.00
% 43.65/33.65  Index Deletion       : 0.00
% 43.65/33.65  Index Matching       : 0.00
% 43.65/33.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
