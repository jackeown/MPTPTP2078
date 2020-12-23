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
% DateTime   : Thu Dec  3 09:57:43 EST 2020

% Result     : Theorem 22.79s
% Output     : CNFRefutation 22.91s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 152 expanded)
%              Number of leaves         :   26 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :  142 ( 355 expanded)
%              Number of equality atoms :   15 (  37 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_8 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(A))
                 => ( r2_hidden(D,B)
                  <=> r2_hidden(D,C) ) )
             => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_setfam_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( ! [C] :
            ( m1_subset_1(C,A)
           => r2_hidden(C,B) )
       => A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_36,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_119,plain,(
    ! [A_53,B_54] :
      ( ~ r2_hidden('#skF_2'(A_53,B_54),B_54)
      | r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_133,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_119])).

tff(c_90,plain,(
    ! [A_47,B_48] :
      ( r2_hidden('#skF_2'(A_47,B_48),A_47)
      | r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14,plain,(
    ! [C_15,A_11] :
      ( r1_tarski(C_15,A_11)
      | ~ r2_hidden(C_15,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_101,plain,(
    ! [A_11,B_48] :
      ( r1_tarski('#skF_2'(k1_zfmisc_1(A_11),B_48),A_11)
      | r1_tarski(k1_zfmisc_1(A_11),B_48) ) ),
    inference(resolution,[status(thm)],[c_90,c_14])).

tff(c_159,plain,(
    ! [C_60,B_61,A_62] :
      ( r2_hidden(C_60,B_61)
      | ~ r2_hidden(C_60,A_62)
      | ~ r1_tarski(A_62,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2630,plain,(
    ! [A_198,B_199,B_200] :
      ( r2_hidden('#skF_2'(A_198,B_199),B_200)
      | ~ r1_tarski(A_198,B_200)
      | r1_tarski(A_198,B_199) ) ),
    inference(resolution,[status(thm)],[c_10,c_159])).

tff(c_40,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_213,plain,(
    ! [A_69,C_70,B_71] :
      ( m1_subset_1(A_69,C_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(C_70))
      | ~ r2_hidden(A_69,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_265,plain,(
    ! [A_74] :
      ( m1_subset_1(A_74,k1_zfmisc_1('#skF_6'))
      | ~ r2_hidden(A_74,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_40,c_213])).

tff(c_44,plain,(
    ! [D_30] :
      ( r2_hidden(D_30,'#skF_8')
      | ~ r2_hidden(D_30,'#skF_7')
      | ~ m1_subset_1(D_30,k1_zfmisc_1('#skF_6')) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_272,plain,(
    ! [A_74] :
      ( r2_hidden(A_74,'#skF_8')
      | ~ r2_hidden(A_74,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_265,c_44])).

tff(c_3100,plain,(
    ! [A_216,B_217] :
      ( r2_hidden('#skF_2'(A_216,B_217),'#skF_8')
      | ~ r1_tarski(A_216,'#skF_7')
      | r1_tarski(A_216,B_217) ) ),
    inference(resolution,[status(thm)],[c_2630,c_272])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3143,plain,(
    ! [A_218] :
      ( ~ r1_tarski(A_218,'#skF_7')
      | r1_tarski(A_218,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_3100,c_8])).

tff(c_19945,plain,(
    ! [B_552] :
      ( r1_tarski('#skF_2'(k1_zfmisc_1('#skF_7'),B_552),'#skF_8')
      | r1_tarski(k1_zfmisc_1('#skF_7'),B_552) ) ),
    inference(resolution,[status(thm)],[c_101,c_3143])).

tff(c_16,plain,(
    ! [C_15,A_11] :
      ( r2_hidden(C_15,k1_zfmisc_1(A_11))
      | ~ r1_tarski(C_15,A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_134,plain,(
    ! [A_53,A_11] :
      ( r1_tarski(A_53,k1_zfmisc_1(A_11))
      | ~ r1_tarski('#skF_2'(A_53,k1_zfmisc_1(A_11)),A_11) ) ),
    inference(resolution,[status(thm)],[c_16,c_119])).

tff(c_20004,plain,(
    r1_tarski(k1_zfmisc_1('#skF_7'),k1_zfmisc_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_19945,c_134])).

tff(c_58,plain,(
    ! [C_38,A_39] :
      ( r2_hidden(C_38,k1_zfmisc_1(A_39))
      | ~ r1_tarski(C_38,A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,B_20)
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_65,plain,(
    ! [C_38,A_39] :
      ( m1_subset_1(C_38,k1_zfmisc_1(A_39))
      | ~ r1_tarski(C_38,A_39) ) ),
    inference(resolution,[status(thm)],[c_58,c_30])).

tff(c_713,plain,(
    ! [A_102,A_103,C_104] :
      ( m1_subset_1(A_102,A_103)
      | ~ r2_hidden(A_102,C_104)
      | ~ r1_tarski(C_104,A_103) ) ),
    inference(resolution,[status(thm)],[c_65,c_213])).

tff(c_745,plain,(
    ! [C_15,A_103,A_11] :
      ( m1_subset_1(C_15,A_103)
      | ~ r1_tarski(k1_zfmisc_1(A_11),A_103)
      | ~ r1_tarski(C_15,A_11) ) ),
    inference(resolution,[status(thm)],[c_16,c_713])).

tff(c_20052,plain,(
    ! [C_15] :
      ( m1_subset_1(C_15,k1_zfmisc_1('#skF_8'))
      | ~ r1_tarski(C_15,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_20004,c_745])).

tff(c_28,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1('#skF_5'(A_16,B_17),A_16)
      | B_17 = A_16
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_38,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_235,plain,(
    ! [A_72] :
      ( m1_subset_1(A_72,k1_zfmisc_1('#skF_6'))
      | ~ r2_hidden(A_72,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_38,c_213])).

tff(c_42,plain,(
    ! [D_30] :
      ( r2_hidden(D_30,'#skF_7')
      | ~ r2_hidden(D_30,'#skF_8')
      | ~ m1_subset_1(D_30,k1_zfmisc_1('#skF_6')) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_247,plain,(
    ! [A_73] :
      ( r2_hidden(A_73,'#skF_7')
      | ~ r2_hidden(A_73,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_235,c_42])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_263,plain,(
    ! [A_73] :
      ( ~ v1_xboole_0('#skF_7')
      | ~ r2_hidden(A_73,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_247,c_2])).

tff(c_264,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_263])).

tff(c_273,plain,(
    ! [A_75] :
      ( r2_hidden(A_75,'#skF_8')
      | ~ r2_hidden(A_75,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_265,c_44])).

tff(c_292,plain,
    ( r2_hidden('#skF_1'('#skF_7'),'#skF_8')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_4,c_273])).

tff(c_301,plain,(
    r2_hidden('#skF_1'('#skF_7'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_264,c_292])).

tff(c_312,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_301,c_2])).

tff(c_32,plain,(
    ! [A_21,B_22] :
      ( r2_hidden(A_21,B_22)
      | v1_xboole_0(B_22)
      | ~ m1_subset_1(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_246,plain,(
    ! [A_72] :
      ( r2_hidden(A_72,'#skF_7')
      | ~ r2_hidden(A_72,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_235,c_42])).

tff(c_313,plain,(
    ! [A_76,B_77] :
      ( ~ r2_hidden('#skF_5'(A_76,B_77),B_77)
      | B_77 = A_76
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1377,plain,(
    ! [A_145] :
      ( A_145 = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_145))
      | ~ r2_hidden('#skF_5'(A_145,'#skF_7'),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_246,c_313])).

tff(c_1389,plain,(
    ! [A_145] :
      ( A_145 = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_145))
      | v1_xboole_0('#skF_8')
      | ~ m1_subset_1('#skF_5'(A_145,'#skF_7'),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_32,c_1377])).

tff(c_53291,plain,(
    ! [A_928] :
      ( A_928 = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_928))
      | ~ m1_subset_1('#skF_5'(A_928,'#skF_7'),'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_312,c_1389])).

tff(c_53295,plain,
    ( '#skF_7' = '#skF_8'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_28,c_53291])).

tff(c_53298,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_36,c_53295])).

tff(c_53301,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_20052,c_53298])).

tff(c_53308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_53301])).

tff(c_53337,plain,(
    ! [A_931] : ~ r2_hidden(A_931,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_263])).

tff(c_53357,plain,(
    v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_4,c_53337])).

tff(c_53310,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_263])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_53330,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_53310,c_12])).

tff(c_53385,plain,(
    ! [A_934] :
      ( A_934 = '#skF_7'
      | ~ v1_xboole_0(A_934) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53330,c_12])).

tff(c_53388,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_53357,c_53385])).

tff(c_53395,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_53388])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:58:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.79/14.00  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.79/14.01  
% 22.79/14.01  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.87/14.01  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_8 > #skF_2 > #skF_5 > #skF_4
% 22.87/14.01  
% 22.87/14.01  %Foreground sorts:
% 22.87/14.01  
% 22.87/14.01  
% 22.87/14.01  %Background operators:
% 22.87/14.01  
% 22.87/14.01  
% 22.87/14.01  %Foreground operators:
% 22.87/14.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.87/14.01  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 22.87/14.01  tff('#skF_1', type, '#skF_1': $i > $i).
% 22.87/14.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 22.87/14.01  tff('#skF_7', type, '#skF_7': $i).
% 22.87/14.01  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 22.87/14.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 22.87/14.01  tff('#skF_6', type, '#skF_6': $i).
% 22.87/14.01  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 22.87/14.01  tff('#skF_8', type, '#skF_8': $i).
% 22.87/14.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.87/14.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.87/14.01  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 22.87/14.01  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 22.87/14.01  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 22.87/14.01  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 22.87/14.01  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 22.87/14.01  
% 22.91/14.03  tff(f_89, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_setfam_1)).
% 22.91/14.03  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 22.91/14.03  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 22.91/14.03  tff(f_49, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 22.91/14.03  tff(f_74, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 22.91/14.03  tff(f_62, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 22.91/14.03  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_subset_1)).
% 22.91/14.03  tff(f_68, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 22.91/14.03  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 22.91/14.03  tff(c_36, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_89])).
% 22.91/14.03  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 22.91/14.03  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 22.91/14.03  tff(c_119, plain, (![A_53, B_54]: (~r2_hidden('#skF_2'(A_53, B_54), B_54) | r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_38])).
% 22.91/14.03  tff(c_133, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_119])).
% 22.91/14.03  tff(c_90, plain, (![A_47, B_48]: (r2_hidden('#skF_2'(A_47, B_48), A_47) | r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_38])).
% 22.91/14.03  tff(c_14, plain, (![C_15, A_11]: (r1_tarski(C_15, A_11) | ~r2_hidden(C_15, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 22.91/14.03  tff(c_101, plain, (![A_11, B_48]: (r1_tarski('#skF_2'(k1_zfmisc_1(A_11), B_48), A_11) | r1_tarski(k1_zfmisc_1(A_11), B_48))), inference(resolution, [status(thm)], [c_90, c_14])).
% 22.91/14.03  tff(c_159, plain, (![C_60, B_61, A_62]: (r2_hidden(C_60, B_61) | ~r2_hidden(C_60, A_62) | ~r1_tarski(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_38])).
% 22.91/14.03  tff(c_2630, plain, (![A_198, B_199, B_200]: (r2_hidden('#skF_2'(A_198, B_199), B_200) | ~r1_tarski(A_198, B_200) | r1_tarski(A_198, B_199))), inference(resolution, [status(thm)], [c_10, c_159])).
% 22.91/14.03  tff(c_40, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 22.91/14.03  tff(c_213, plain, (![A_69, C_70, B_71]: (m1_subset_1(A_69, C_70) | ~m1_subset_1(B_71, k1_zfmisc_1(C_70)) | ~r2_hidden(A_69, B_71))), inference(cnfTransformation, [status(thm)], [f_74])).
% 22.91/14.03  tff(c_265, plain, (![A_74]: (m1_subset_1(A_74, k1_zfmisc_1('#skF_6')) | ~r2_hidden(A_74, '#skF_7'))), inference(resolution, [status(thm)], [c_40, c_213])).
% 22.91/14.03  tff(c_44, plain, (![D_30]: (r2_hidden(D_30, '#skF_8') | ~r2_hidden(D_30, '#skF_7') | ~m1_subset_1(D_30, k1_zfmisc_1('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 22.91/14.03  tff(c_272, plain, (![A_74]: (r2_hidden(A_74, '#skF_8') | ~r2_hidden(A_74, '#skF_7'))), inference(resolution, [status(thm)], [c_265, c_44])).
% 22.91/14.03  tff(c_3100, plain, (![A_216, B_217]: (r2_hidden('#skF_2'(A_216, B_217), '#skF_8') | ~r1_tarski(A_216, '#skF_7') | r1_tarski(A_216, B_217))), inference(resolution, [status(thm)], [c_2630, c_272])).
% 22.91/14.03  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 22.91/14.03  tff(c_3143, plain, (![A_218]: (~r1_tarski(A_218, '#skF_7') | r1_tarski(A_218, '#skF_8'))), inference(resolution, [status(thm)], [c_3100, c_8])).
% 22.91/14.03  tff(c_19945, plain, (![B_552]: (r1_tarski('#skF_2'(k1_zfmisc_1('#skF_7'), B_552), '#skF_8') | r1_tarski(k1_zfmisc_1('#skF_7'), B_552))), inference(resolution, [status(thm)], [c_101, c_3143])).
% 22.91/14.03  tff(c_16, plain, (![C_15, A_11]: (r2_hidden(C_15, k1_zfmisc_1(A_11)) | ~r1_tarski(C_15, A_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 22.91/14.03  tff(c_134, plain, (![A_53, A_11]: (r1_tarski(A_53, k1_zfmisc_1(A_11)) | ~r1_tarski('#skF_2'(A_53, k1_zfmisc_1(A_11)), A_11))), inference(resolution, [status(thm)], [c_16, c_119])).
% 22.91/14.03  tff(c_20004, plain, (r1_tarski(k1_zfmisc_1('#skF_7'), k1_zfmisc_1('#skF_8'))), inference(resolution, [status(thm)], [c_19945, c_134])).
% 22.91/14.03  tff(c_58, plain, (![C_38, A_39]: (r2_hidden(C_38, k1_zfmisc_1(A_39)) | ~r1_tarski(C_38, A_39))), inference(cnfTransformation, [status(thm)], [f_49])).
% 22.91/14.03  tff(c_30, plain, (![A_19, B_20]: (m1_subset_1(A_19, B_20) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_62])).
% 22.91/14.03  tff(c_65, plain, (![C_38, A_39]: (m1_subset_1(C_38, k1_zfmisc_1(A_39)) | ~r1_tarski(C_38, A_39))), inference(resolution, [status(thm)], [c_58, c_30])).
% 22.91/14.03  tff(c_713, plain, (![A_102, A_103, C_104]: (m1_subset_1(A_102, A_103) | ~r2_hidden(A_102, C_104) | ~r1_tarski(C_104, A_103))), inference(resolution, [status(thm)], [c_65, c_213])).
% 22.91/14.03  tff(c_745, plain, (![C_15, A_103, A_11]: (m1_subset_1(C_15, A_103) | ~r1_tarski(k1_zfmisc_1(A_11), A_103) | ~r1_tarski(C_15, A_11))), inference(resolution, [status(thm)], [c_16, c_713])).
% 22.91/14.03  tff(c_20052, plain, (![C_15]: (m1_subset_1(C_15, k1_zfmisc_1('#skF_8')) | ~r1_tarski(C_15, '#skF_7'))), inference(resolution, [status(thm)], [c_20004, c_745])).
% 22.91/14.03  tff(c_28, plain, (![A_16, B_17]: (m1_subset_1('#skF_5'(A_16, B_17), A_16) | B_17=A_16 | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 22.91/14.03  tff(c_38, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k1_zfmisc_1('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 22.91/14.03  tff(c_235, plain, (![A_72]: (m1_subset_1(A_72, k1_zfmisc_1('#skF_6')) | ~r2_hidden(A_72, '#skF_8'))), inference(resolution, [status(thm)], [c_38, c_213])).
% 22.91/14.03  tff(c_42, plain, (![D_30]: (r2_hidden(D_30, '#skF_7') | ~r2_hidden(D_30, '#skF_8') | ~m1_subset_1(D_30, k1_zfmisc_1('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 22.91/14.03  tff(c_247, plain, (![A_73]: (r2_hidden(A_73, '#skF_7') | ~r2_hidden(A_73, '#skF_8'))), inference(resolution, [status(thm)], [c_235, c_42])).
% 22.91/14.03  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 22.91/14.03  tff(c_263, plain, (![A_73]: (~v1_xboole_0('#skF_7') | ~r2_hidden(A_73, '#skF_8'))), inference(resolution, [status(thm)], [c_247, c_2])).
% 22.91/14.03  tff(c_264, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_263])).
% 22.91/14.03  tff(c_273, plain, (![A_75]: (r2_hidden(A_75, '#skF_8') | ~r2_hidden(A_75, '#skF_7'))), inference(resolution, [status(thm)], [c_265, c_44])).
% 22.91/14.03  tff(c_292, plain, (r2_hidden('#skF_1'('#skF_7'), '#skF_8') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_4, c_273])).
% 22.91/14.03  tff(c_301, plain, (r2_hidden('#skF_1'('#skF_7'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_264, c_292])).
% 22.91/14.03  tff(c_312, plain, (~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_301, c_2])).
% 22.91/14.03  tff(c_32, plain, (![A_21, B_22]: (r2_hidden(A_21, B_22) | v1_xboole_0(B_22) | ~m1_subset_1(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_68])).
% 22.91/14.03  tff(c_246, plain, (![A_72]: (r2_hidden(A_72, '#skF_7') | ~r2_hidden(A_72, '#skF_8'))), inference(resolution, [status(thm)], [c_235, c_42])).
% 22.91/14.03  tff(c_313, plain, (![A_76, B_77]: (~r2_hidden('#skF_5'(A_76, B_77), B_77) | B_77=A_76 | ~m1_subset_1(B_77, k1_zfmisc_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 22.91/14.03  tff(c_1377, plain, (![A_145]: (A_145='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_145)) | ~r2_hidden('#skF_5'(A_145, '#skF_7'), '#skF_8'))), inference(resolution, [status(thm)], [c_246, c_313])).
% 22.91/14.03  tff(c_1389, plain, (![A_145]: (A_145='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_145)) | v1_xboole_0('#skF_8') | ~m1_subset_1('#skF_5'(A_145, '#skF_7'), '#skF_8'))), inference(resolution, [status(thm)], [c_32, c_1377])).
% 22.91/14.03  tff(c_53291, plain, (![A_928]: (A_928='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_928)) | ~m1_subset_1('#skF_5'(A_928, '#skF_7'), '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_312, c_1389])).
% 22.91/14.03  tff(c_53295, plain, ('#skF_7'='#skF_8' | ~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_8'))), inference(resolution, [status(thm)], [c_28, c_53291])).
% 22.91/14.03  tff(c_53298, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_36, c_36, c_53295])).
% 22.91/14.03  tff(c_53301, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_20052, c_53298])).
% 22.91/14.03  tff(c_53308, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_133, c_53301])).
% 22.91/14.03  tff(c_53337, plain, (![A_931]: (~r2_hidden(A_931, '#skF_8'))), inference(splitRight, [status(thm)], [c_263])).
% 22.91/14.03  tff(c_53357, plain, (v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_4, c_53337])).
% 22.91/14.03  tff(c_53310, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_263])).
% 22.91/14.03  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 22.91/14.03  tff(c_53330, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_53310, c_12])).
% 22.91/14.03  tff(c_53385, plain, (![A_934]: (A_934='#skF_7' | ~v1_xboole_0(A_934))), inference(demodulation, [status(thm), theory('equality')], [c_53330, c_12])).
% 22.91/14.03  tff(c_53388, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_53357, c_53385])).
% 22.91/14.03  tff(c_53395, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_53388])).
% 22.91/14.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.91/14.03  
% 22.91/14.03  Inference rules
% 22.91/14.03  ----------------------
% 22.91/14.03  #Ref     : 0
% 22.91/14.03  #Sup     : 12764
% 22.91/14.03  #Fact    : 0
% 22.91/14.03  #Define  : 0
% 22.91/14.03  #Split   : 49
% 22.91/14.03  #Chain   : 0
% 22.91/14.03  #Close   : 0
% 22.91/14.03  
% 22.91/14.03  Ordering : KBO
% 22.91/14.03  
% 22.91/14.03  Simplification rules
% 22.91/14.03  ----------------------
% 22.91/14.03  #Subsume      : 3935
% 22.91/14.03  #Demod        : 2111
% 22.91/14.03  #Tautology    : 1245
% 22.91/14.03  #SimpNegUnit  : 84
% 22.91/14.03  #BackRed      : 159
% 22.91/14.03  
% 22.91/14.03  #Partial instantiations: 0
% 22.91/14.03  #Strategies tried      : 1
% 22.91/14.03  
% 22.91/14.03  Timing (in seconds)
% 22.91/14.03  ----------------------
% 22.91/14.03  Preprocessing        : 0.38
% 22.91/14.03  Parsing              : 0.20
% 22.91/14.03  CNF conversion       : 0.03
% 22.91/14.03  Main loop            : 12.83
% 22.91/14.03  Inferencing          : 1.66
% 22.91/14.03  Reduction            : 3.93
% 22.91/14.03  Demodulation         : 2.65
% 22.91/14.03  BG Simplification    : 0.17
% 22.91/14.03  Subsumption          : 5.95
% 22.91/14.03  Abstraction          : 0.23
% 22.91/14.03  MUC search           : 0.00
% 22.91/14.03  Cooper               : 0.00
% 22.91/14.03  Total                : 13.25
% 22.91/14.03  Index Insertion      : 0.00
% 22.91/14.03  Index Deletion       : 0.00
% 22.91/14.03  Index Matching       : 0.00
% 22.91/14.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
