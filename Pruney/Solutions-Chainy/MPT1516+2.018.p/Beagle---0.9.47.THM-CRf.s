%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:53 EST 2020

% Result     : Theorem 9.10s
% Output     : CNFRefutation 9.10s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 792 expanded)
%              Number of leaves         :   47 ( 290 expanded)
%              Depth                    :   25
%              Number of atoms          :  529 (3336 expanded)
%              Number of equality atoms :   64 ( 431 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k2_zfmisc_1 > k15_lattice3 > #nlpp > u1_struct_0 > k5_lattices > k1_xboole_0 > #skF_7 > #skF_2 > #skF_4 > #skF_3 > #skF_5 > #skF_8 > #skF_1 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff(k2_lattices,type,(
    k2_lattices: ( $i * $i * $i ) > $i )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k15_lattice3,type,(
    k15_lattice3: ( $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff(r4_lattice3,type,(
    r4_lattice3: ( $i * $i * $i ) > $o )).

tff(v4_lattice3,type,(
    v4_lattice3: $i > $o )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(v13_lattices,type,(
    v13_lattices: $i > $o )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_lattices,type,(
    k5_lattices: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_213,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v13_lattices(A)
          & l3_lattices(A)
          & k5_lattices(A) = k15_lattice3(A,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattice3)).

tff(f_88,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_56,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( ( ~ v2_struct_0(A)
          & v10_lattices(A) )
       => ( ~ v2_struct_0(A)
          & v4_lattices(A)
          & v5_lattices(A)
          & v6_lattices(A)
          & v7_lattices(A)
          & v8_lattices(A)
          & v9_lattices(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

tff(f_192,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k15_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

tff(f_124,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => ( v13_lattices(A)
      <=> ? [B] :
            ( m1_subset_1(B,u1_struct_0(A))
            & ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( k2_lattices(A,B,C) = B
                  & k2_lattices(A,C,B) = B ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_lattices)).

tff(f_142,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( r4_lattice3(A,B,C)
            <=> ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r2_hidden(D,C)
                   => r1_lattices(A,D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_170,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ! [B,C] :
            ( m1_subset_1(C,u1_struct_0(A))
           => ( C = k15_lattice3(A,B)
            <=> ( r4_lattice3(A,C,B)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r4_lattice3(A,D,B)
                     => r1_lattices(A,C,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).

tff(f_107,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_lattices(A,B,C)
              <=> k2_lattices(A,B,C) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).

tff(f_185,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => ( v6_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k2_lattices(A,B,C) = k2_lattices(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_lattices)).

tff(f_82,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => m1_subset_1(k5_lattices(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

tff(f_75,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A) )
     => ( v13_lattices(A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( B = k5_lattices(A)
            <=> ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ( k2_lattices(A,B,C) = B
                    & k2_lattices(A,C,B) = B ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).

tff(c_82,plain,(
    l3_lattices('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_119,plain,(
    ! [A_86] :
      ( l1_lattices(A_86)
      | ~ l3_lattices(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_123,plain,(
    l1_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_82,c_119])).

tff(c_88,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_86,plain,(
    v10_lattices('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_80,plain,
    ( k15_lattice3('#skF_8',k1_xboole_0) != k5_lattices('#skF_8')
    | ~ l3_lattices('#skF_8')
    | ~ v13_lattices('#skF_8')
    | ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_90,plain,
    ( k15_lattice3('#skF_8',k1_xboole_0) != k5_lattices('#skF_8')
    | ~ v13_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_80])).

tff(c_91,plain,
    ( k15_lattice3('#skF_8',k1_xboole_0) != k5_lattices('#skF_8')
    | ~ v13_lattices('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_90])).

tff(c_132,plain,(
    ~ v13_lattices('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_91])).

tff(c_84,plain,(
    v4_lattice3('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_16,plain,(
    ! [A_5] :
      ( v6_lattices(A_5)
      | ~ v10_lattices(A_5)
      | v2_struct_0(A_5)
      | ~ l3_lattices(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12,plain,(
    ! [A_5] :
      ( v8_lattices(A_5)
      | ~ v10_lattices(A_5)
      | v2_struct_0(A_5)
      | ~ l3_lattices(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10,plain,(
    ! [A_5] :
      ( v9_lattices(A_5)
      | ~ v10_lattices(A_5)
      | v2_struct_0(A_5)
      | ~ l3_lattices(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_78,plain,(
    ! [A_81,B_82] :
      ( m1_subset_1(k15_lattice3(A_81,B_82),u1_struct_0(A_81))
      | ~ l3_lattices(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_44,plain,(
    ! [A_25,B_34] :
      ( m1_subset_1('#skF_3'(A_25,B_34),u1_struct_0(A_25))
      | v13_lattices(A_25)
      | ~ m1_subset_1(B_34,u1_struct_0(A_25))
      | ~ l1_lattices(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_258,plain,(
    ! [A_118,B_119,C_120] :
      ( r2_hidden('#skF_4'(A_118,B_119,C_120),C_120)
      | r4_lattice3(A_118,B_119,C_120)
      | ~ m1_subset_1(B_119,u1_struct_0(A_118))
      | ~ l3_lattices(A_118)
      | v2_struct_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_124,plain,(
    ! [A_87,B_88] : ~ r2_hidden(A_87,k2_zfmisc_1(A_87,B_88)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_127,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_124])).

tff(c_264,plain,(
    ! [A_121,B_122] :
      ( r4_lattice3(A_121,B_122,k1_xboole_0)
      | ~ m1_subset_1(B_122,u1_struct_0(A_121))
      | ~ l3_lattices(A_121)
      | v2_struct_0(A_121) ) ),
    inference(resolution,[status(thm)],[c_258,c_127])).

tff(c_283,plain,(
    ! [A_25,B_34] :
      ( r4_lattice3(A_25,'#skF_3'(A_25,B_34),k1_xboole_0)
      | ~ l3_lattices(A_25)
      | v13_lattices(A_25)
      | ~ m1_subset_1(B_34,u1_struct_0(A_25))
      | ~ l1_lattices(A_25)
      | v2_struct_0(A_25) ) ),
    inference(resolution,[status(thm)],[c_44,c_264])).

tff(c_883,plain,(
    ! [A_240,B_241,D_242] :
      ( r1_lattices(A_240,k15_lattice3(A_240,B_241),D_242)
      | ~ r4_lattice3(A_240,D_242,B_241)
      | ~ m1_subset_1(D_242,u1_struct_0(A_240))
      | ~ m1_subset_1(k15_lattice3(A_240,B_241),u1_struct_0(A_240))
      | ~ v4_lattice3(A_240)
      | ~ v10_lattices(A_240)
      | ~ l3_lattices(A_240)
      | v2_struct_0(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_887,plain,(
    ! [A_243,B_244,D_245] :
      ( r1_lattices(A_243,k15_lattice3(A_243,B_244),D_245)
      | ~ r4_lattice3(A_243,D_245,B_244)
      | ~ m1_subset_1(D_245,u1_struct_0(A_243))
      | ~ v4_lattice3(A_243)
      | ~ v10_lattices(A_243)
      | ~ l3_lattices(A_243)
      | v2_struct_0(A_243) ) ),
    inference(resolution,[status(thm)],[c_78,c_883])).

tff(c_40,plain,(
    ! [A_18,B_22,C_24] :
      ( k2_lattices(A_18,B_22,C_24) = B_22
      | ~ r1_lattices(A_18,B_22,C_24)
      | ~ m1_subset_1(C_24,u1_struct_0(A_18))
      | ~ m1_subset_1(B_22,u1_struct_0(A_18))
      | ~ l3_lattices(A_18)
      | ~ v9_lattices(A_18)
      | ~ v8_lattices(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1315,plain,(
    ! [A_319,B_320,D_321] :
      ( k2_lattices(A_319,k15_lattice3(A_319,B_320),D_321) = k15_lattice3(A_319,B_320)
      | ~ m1_subset_1(k15_lattice3(A_319,B_320),u1_struct_0(A_319))
      | ~ v9_lattices(A_319)
      | ~ v8_lattices(A_319)
      | ~ r4_lattice3(A_319,D_321,B_320)
      | ~ m1_subset_1(D_321,u1_struct_0(A_319))
      | ~ v4_lattice3(A_319)
      | ~ v10_lattices(A_319)
      | ~ l3_lattices(A_319)
      | v2_struct_0(A_319) ) ),
    inference(resolution,[status(thm)],[c_887,c_40])).

tff(c_1319,plain,(
    ! [A_322,B_323,D_324] :
      ( k2_lattices(A_322,k15_lattice3(A_322,B_323),D_324) = k15_lattice3(A_322,B_323)
      | ~ v9_lattices(A_322)
      | ~ v8_lattices(A_322)
      | ~ r4_lattice3(A_322,D_324,B_323)
      | ~ m1_subset_1(D_324,u1_struct_0(A_322))
      | ~ v4_lattice3(A_322)
      | ~ v10_lattices(A_322)
      | ~ l3_lattices(A_322)
      | v2_struct_0(A_322) ) ),
    inference(resolution,[status(thm)],[c_78,c_1315])).

tff(c_1341,plain,(
    ! [A_25,B_323,B_34] :
      ( k2_lattices(A_25,k15_lattice3(A_25,B_323),'#skF_3'(A_25,B_34)) = k15_lattice3(A_25,B_323)
      | ~ v9_lattices(A_25)
      | ~ v8_lattices(A_25)
      | ~ r4_lattice3(A_25,'#skF_3'(A_25,B_34),B_323)
      | ~ v4_lattice3(A_25)
      | ~ v10_lattices(A_25)
      | ~ l3_lattices(A_25)
      | v13_lattices(A_25)
      | ~ m1_subset_1(B_34,u1_struct_0(A_25))
      | ~ l1_lattices(A_25)
      | v2_struct_0(A_25) ) ),
    inference(resolution,[status(thm)],[c_44,c_1319])).

tff(c_1447,plain,(
    ! [A_342,B_343,B_344] :
      ( k2_lattices(A_342,k15_lattice3(A_342,B_343),'#skF_3'(A_342,B_344)) = k15_lattice3(A_342,B_343)
      | ~ v9_lattices(A_342)
      | ~ v8_lattices(A_342)
      | ~ r4_lattice3(A_342,'#skF_3'(A_342,B_344),B_343)
      | ~ v4_lattice3(A_342)
      | ~ v10_lattices(A_342)
      | ~ l3_lattices(A_342)
      | v13_lattices(A_342)
      | ~ m1_subset_1(B_344,u1_struct_0(A_342))
      | ~ l1_lattices(A_342)
      | v2_struct_0(A_342) ) ),
    inference(resolution,[status(thm)],[c_44,c_1319])).

tff(c_399,plain,(
    ! [A_155,C_156,B_157] :
      ( k2_lattices(A_155,C_156,B_157) = k2_lattices(A_155,B_157,C_156)
      | ~ m1_subset_1(C_156,u1_struct_0(A_155))
      | ~ m1_subset_1(B_157,u1_struct_0(A_155))
      | ~ v6_lattices(A_155)
      | ~ l1_lattices(A_155)
      | v2_struct_0(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_948,plain,(
    ! [A_261,B_262,B_263] :
      ( k2_lattices(A_261,B_262,'#skF_3'(A_261,B_263)) = k2_lattices(A_261,'#skF_3'(A_261,B_263),B_262)
      | ~ m1_subset_1(B_262,u1_struct_0(A_261))
      | ~ v6_lattices(A_261)
      | v13_lattices(A_261)
      | ~ m1_subset_1(B_263,u1_struct_0(A_261))
      | ~ l1_lattices(A_261)
      | v2_struct_0(A_261) ) ),
    inference(resolution,[status(thm)],[c_44,c_399])).

tff(c_974,plain,(
    ! [A_81,B_82,B_263] :
      ( k2_lattices(A_81,k15_lattice3(A_81,B_82),'#skF_3'(A_81,B_263)) = k2_lattices(A_81,'#skF_3'(A_81,B_263),k15_lattice3(A_81,B_82))
      | ~ v6_lattices(A_81)
      | v13_lattices(A_81)
      | ~ m1_subset_1(B_263,u1_struct_0(A_81))
      | ~ l1_lattices(A_81)
      | ~ l3_lattices(A_81)
      | v2_struct_0(A_81) ) ),
    inference(resolution,[status(thm)],[c_78,c_948])).

tff(c_2217,plain,(
    ! [A_513,B_514,B_515] :
      ( k2_lattices(A_513,'#skF_3'(A_513,B_514),k15_lattice3(A_513,B_515)) = k15_lattice3(A_513,B_515)
      | ~ v6_lattices(A_513)
      | v13_lattices(A_513)
      | ~ m1_subset_1(B_514,u1_struct_0(A_513))
      | ~ l1_lattices(A_513)
      | ~ l3_lattices(A_513)
      | v2_struct_0(A_513)
      | ~ v9_lattices(A_513)
      | ~ v8_lattices(A_513)
      | ~ r4_lattice3(A_513,'#skF_3'(A_513,B_514),B_515)
      | ~ v4_lattice3(A_513)
      | ~ v10_lattices(A_513)
      | ~ l3_lattices(A_513)
      | v13_lattices(A_513)
      | ~ m1_subset_1(B_514,u1_struct_0(A_513))
      | ~ l1_lattices(A_513)
      | v2_struct_0(A_513) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1447,c_974])).

tff(c_42,plain,(
    ! [A_25,B_34] :
      ( k2_lattices(A_25,'#skF_3'(A_25,B_34),B_34) != B_34
      | k2_lattices(A_25,B_34,'#skF_3'(A_25,B_34)) != B_34
      | v13_lattices(A_25)
      | ~ m1_subset_1(B_34,u1_struct_0(A_25))
      | ~ l1_lattices(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2236,plain,(
    ! [A_516,B_517] :
      ( k2_lattices(A_516,k15_lattice3(A_516,B_517),'#skF_3'(A_516,k15_lattice3(A_516,B_517))) != k15_lattice3(A_516,B_517)
      | ~ v6_lattices(A_516)
      | ~ v9_lattices(A_516)
      | ~ v8_lattices(A_516)
      | ~ r4_lattice3(A_516,'#skF_3'(A_516,k15_lattice3(A_516,B_517)),B_517)
      | ~ v4_lattice3(A_516)
      | ~ v10_lattices(A_516)
      | ~ l3_lattices(A_516)
      | v13_lattices(A_516)
      | ~ m1_subset_1(k15_lattice3(A_516,B_517),u1_struct_0(A_516))
      | ~ l1_lattices(A_516)
      | v2_struct_0(A_516) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2217,c_42])).

tff(c_2242,plain,(
    ! [A_518,B_519] :
      ( ~ v6_lattices(A_518)
      | ~ v9_lattices(A_518)
      | ~ v8_lattices(A_518)
      | ~ r4_lattice3(A_518,'#skF_3'(A_518,k15_lattice3(A_518,B_519)),B_519)
      | ~ v4_lattice3(A_518)
      | ~ v10_lattices(A_518)
      | ~ l3_lattices(A_518)
      | v13_lattices(A_518)
      | ~ m1_subset_1(k15_lattice3(A_518,B_519),u1_struct_0(A_518))
      | ~ l1_lattices(A_518)
      | v2_struct_0(A_518) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1341,c_2236])).

tff(c_2248,plain,(
    ! [A_520] :
      ( ~ v6_lattices(A_520)
      | ~ v9_lattices(A_520)
      | ~ v8_lattices(A_520)
      | ~ v4_lattice3(A_520)
      | ~ v10_lattices(A_520)
      | ~ l3_lattices(A_520)
      | v13_lattices(A_520)
      | ~ m1_subset_1(k15_lattice3(A_520,k1_xboole_0),u1_struct_0(A_520))
      | ~ l1_lattices(A_520)
      | v2_struct_0(A_520) ) ),
    inference(resolution,[status(thm)],[c_283,c_2242])).

tff(c_2254,plain,(
    ! [A_521] :
      ( ~ v6_lattices(A_521)
      | ~ v9_lattices(A_521)
      | ~ v8_lattices(A_521)
      | ~ v4_lattice3(A_521)
      | ~ v10_lattices(A_521)
      | v13_lattices(A_521)
      | ~ l1_lattices(A_521)
      | ~ l3_lattices(A_521)
      | v2_struct_0(A_521) ) ),
    inference(resolution,[status(thm)],[c_78,c_2248])).

tff(c_2259,plain,(
    ! [A_522] :
      ( ~ v6_lattices(A_522)
      | ~ v8_lattices(A_522)
      | ~ v4_lattice3(A_522)
      | v13_lattices(A_522)
      | ~ l1_lattices(A_522)
      | ~ v10_lattices(A_522)
      | v2_struct_0(A_522)
      | ~ l3_lattices(A_522) ) ),
    inference(resolution,[status(thm)],[c_10,c_2254])).

tff(c_2264,plain,(
    ! [A_523] :
      ( ~ v6_lattices(A_523)
      | ~ v4_lattice3(A_523)
      | v13_lattices(A_523)
      | ~ l1_lattices(A_523)
      | ~ v10_lattices(A_523)
      | v2_struct_0(A_523)
      | ~ l3_lattices(A_523) ) ),
    inference(resolution,[status(thm)],[c_12,c_2259])).

tff(c_2269,plain,(
    ! [A_524] :
      ( ~ v4_lattice3(A_524)
      | v13_lattices(A_524)
      | ~ l1_lattices(A_524)
      | ~ v10_lattices(A_524)
      | v2_struct_0(A_524)
      | ~ l3_lattices(A_524) ) ),
    inference(resolution,[status(thm)],[c_16,c_2264])).

tff(c_2272,plain,
    ( v13_lattices('#skF_8')
    | ~ l1_lattices('#skF_8')
    | ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8')
    | ~ l3_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_84,c_2269])).

tff(c_2275,plain,
    ( v13_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_86,c_123,c_2272])).

tff(c_2277,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_132,c_2275])).

tff(c_2279,plain,(
    v13_lattices('#skF_8') ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_32,plain,(
    ! [A_16] :
      ( m1_subset_1(k5_lattices(A_16),u1_struct_0(A_16))
      | ~ l1_lattices(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_46,plain,(
    ! [A_25] :
      ( m1_subset_1('#skF_2'(A_25),u1_struct_0(A_25))
      | ~ v13_lattices(A_25)
      | ~ l1_lattices(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2556,plain,(
    ! [A_593,C_594] :
      ( k2_lattices(A_593,k5_lattices(A_593),C_594) = k5_lattices(A_593)
      | ~ m1_subset_1(C_594,u1_struct_0(A_593))
      | ~ m1_subset_1(k5_lattices(A_593),u1_struct_0(A_593))
      | ~ v13_lattices(A_593)
      | ~ l1_lattices(A_593)
      | v2_struct_0(A_593) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2581,plain,(
    ! [A_595] :
      ( k2_lattices(A_595,k5_lattices(A_595),'#skF_2'(A_595)) = k5_lattices(A_595)
      | ~ m1_subset_1(k5_lattices(A_595),u1_struct_0(A_595))
      | ~ v13_lattices(A_595)
      | ~ l1_lattices(A_595)
      | v2_struct_0(A_595) ) ),
    inference(resolution,[status(thm)],[c_46,c_2556])).

tff(c_2585,plain,(
    ! [A_596] :
      ( k2_lattices(A_596,k5_lattices(A_596),'#skF_2'(A_596)) = k5_lattices(A_596)
      | ~ v13_lattices(A_596)
      | ~ l1_lattices(A_596)
      | v2_struct_0(A_596) ) ),
    inference(resolution,[status(thm)],[c_32,c_2581])).

tff(c_2322,plain,(
    ! [A_543,C_544] :
      ( k2_lattices(A_543,C_544,'#skF_2'(A_543)) = '#skF_2'(A_543)
      | ~ m1_subset_1(C_544,u1_struct_0(A_543))
      | ~ v13_lattices(A_543)
      | ~ l1_lattices(A_543)
      | v2_struct_0(A_543) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2340,plain,(
    ! [A_16] :
      ( k2_lattices(A_16,k5_lattices(A_16),'#skF_2'(A_16)) = '#skF_2'(A_16)
      | ~ v13_lattices(A_16)
      | ~ l1_lattices(A_16)
      | v2_struct_0(A_16) ) ),
    inference(resolution,[status(thm)],[c_32,c_2322])).

tff(c_2594,plain,(
    ! [A_596] :
      ( k5_lattices(A_596) = '#skF_2'(A_596)
      | ~ v13_lattices(A_596)
      | ~ l1_lattices(A_596)
      | v2_struct_0(A_596)
      | ~ v13_lattices(A_596)
      | ~ l1_lattices(A_596)
      | v2_struct_0(A_596) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2585,c_2340])).

tff(c_2644,plain,(
    ! [A_600] :
      ( k5_lattices(A_600) = '#skF_2'(A_600)
      | ~ v13_lattices(A_600)
      | ~ l1_lattices(A_600)
      | v2_struct_0(A_600) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_2594])).

tff(c_2647,plain,
    ( k5_lattices('#skF_8') = '#skF_2'('#skF_8')
    | ~ v13_lattices('#skF_8')
    | ~ l1_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_2644,c_88])).

tff(c_2650,plain,(
    k5_lattices('#skF_8') = '#skF_2'('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_2279,c_2647])).

tff(c_2278,plain,(
    k15_lattice3('#skF_8',k1_xboole_0) != k5_lattices('#skF_8') ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_2651,plain,(
    k15_lattice3('#skF_8',k1_xboole_0) != '#skF_2'('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2650,c_2278])).

tff(c_2405,plain,(
    ! [A_553,B_554,C_555] :
      ( r2_hidden('#skF_4'(A_553,B_554,C_555),C_555)
      | r4_lattice3(A_553,B_554,C_555)
      | ~ m1_subset_1(B_554,u1_struct_0(A_553))
      | ~ l3_lattices(A_553)
      | v2_struct_0(A_553) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_2411,plain,(
    ! [A_556,B_557] :
      ( r4_lattice3(A_556,B_557,k1_xboole_0)
      | ~ m1_subset_1(B_557,u1_struct_0(A_556))
      | ~ l3_lattices(A_556)
      | v2_struct_0(A_556) ) ),
    inference(resolution,[status(thm)],[c_2405,c_127])).

tff(c_2435,plain,(
    ! [A_16] :
      ( r4_lattice3(A_16,k5_lattices(A_16),k1_xboole_0)
      | ~ l3_lattices(A_16)
      | ~ l1_lattices(A_16)
      | v2_struct_0(A_16) ) ),
    inference(resolution,[status(thm)],[c_32,c_2411])).

tff(c_2661,plain,
    ( r4_lattice3('#skF_8','#skF_2'('#skF_8'),k1_xboole_0)
    | ~ l3_lattices('#skF_8')
    | ~ l1_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_2650,c_2435])).

tff(c_2680,plain,
    ( r4_lattice3('#skF_8','#skF_2'('#skF_8'),k1_xboole_0)
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_82,c_2661])).

tff(c_2681,plain,(
    r4_lattice3('#skF_8','#skF_2'('#skF_8'),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_2680])).

tff(c_2670,plain,
    ( m1_subset_1('#skF_2'('#skF_8'),u1_struct_0('#skF_8'))
    | ~ l1_lattices('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_2650,c_32])).

tff(c_2689,plain,
    ( m1_subset_1('#skF_2'('#skF_8'),u1_struct_0('#skF_8'))
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_2670])).

tff(c_2690,plain,(
    m1_subset_1('#skF_2'('#skF_8'),u1_struct_0('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_2689])).

tff(c_3039,plain,(
    ! [A_623,B_624,C_625] :
      ( r1_lattices(A_623,B_624,C_625)
      | k2_lattices(A_623,B_624,C_625) != B_624
      | ~ m1_subset_1(C_625,u1_struct_0(A_623))
      | ~ m1_subset_1(B_624,u1_struct_0(A_623))
      | ~ l3_lattices(A_623)
      | ~ v9_lattices(A_623)
      | ~ v8_lattices(A_623)
      | v2_struct_0(A_623) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_3041,plain,(
    ! [B_624] :
      ( r1_lattices('#skF_8',B_624,'#skF_2'('#skF_8'))
      | k2_lattices('#skF_8',B_624,'#skF_2'('#skF_8')) != B_624
      | ~ m1_subset_1(B_624,u1_struct_0('#skF_8'))
      | ~ l3_lattices('#skF_8')
      | ~ v9_lattices('#skF_8')
      | ~ v8_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2690,c_3039])).

tff(c_3060,plain,(
    ! [B_624] :
      ( r1_lattices('#skF_8',B_624,'#skF_2'('#skF_8'))
      | k2_lattices('#skF_8',B_624,'#skF_2'('#skF_8')) != B_624
      | ~ m1_subset_1(B_624,u1_struct_0('#skF_8'))
      | ~ v9_lattices('#skF_8')
      | ~ v8_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_3041])).

tff(c_3061,plain,(
    ! [B_624] :
      ( r1_lattices('#skF_8',B_624,'#skF_2'('#skF_8'))
      | k2_lattices('#skF_8',B_624,'#skF_2'('#skF_8')) != B_624
      | ~ m1_subset_1(B_624,u1_struct_0('#skF_8'))
      | ~ v9_lattices('#skF_8')
      | ~ v8_lattices('#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_3060])).

tff(c_3070,plain,(
    ~ v8_lattices('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_3061])).

tff(c_3073,plain,
    ( ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8')
    | ~ l3_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_12,c_3070])).

tff(c_3076,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_86,c_3073])).

tff(c_3078,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_3076])).

tff(c_3080,plain,(
    v8_lattices('#skF_8') ),
    inference(splitRight,[status(thm)],[c_3061])).

tff(c_3079,plain,(
    ! [B_624] :
      ( ~ v9_lattices('#skF_8')
      | r1_lattices('#skF_8',B_624,'#skF_2'('#skF_8'))
      | k2_lattices('#skF_8',B_624,'#skF_2'('#skF_8')) != B_624
      | ~ m1_subset_1(B_624,u1_struct_0('#skF_8')) ) ),
    inference(splitRight,[status(thm)],[c_3061])).

tff(c_3098,plain,(
    ~ v9_lattices('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_3079])).

tff(c_3101,plain,
    ( ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8')
    | ~ l3_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_10,c_3098])).

tff(c_3104,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_86,c_3101])).

tff(c_3106,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_3104])).

tff(c_3108,plain,(
    v9_lattices('#skF_8') ),
    inference(splitRight,[status(thm)],[c_3079])).

tff(c_70,plain,(
    ! [A_70,C_79,B_77] :
      ( k2_lattices(A_70,C_79,B_77) = k2_lattices(A_70,B_77,C_79)
      | ~ m1_subset_1(C_79,u1_struct_0(A_70))
      | ~ m1_subset_1(B_77,u1_struct_0(A_70))
      | ~ v6_lattices(A_70)
      | ~ l1_lattices(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_2699,plain,(
    ! [B_77] :
      ( k2_lattices('#skF_8',B_77,'#skF_2'('#skF_8')) = k2_lattices('#skF_8','#skF_2'('#skF_8'),B_77)
      | ~ m1_subset_1(B_77,u1_struct_0('#skF_8'))
      | ~ v6_lattices('#skF_8')
      | ~ l1_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2690,c_70])).

tff(c_2721,plain,(
    ! [B_77] :
      ( k2_lattices('#skF_8',B_77,'#skF_2'('#skF_8')) = k2_lattices('#skF_8','#skF_2'('#skF_8'),B_77)
      | ~ m1_subset_1(B_77,u1_struct_0('#skF_8'))
      | ~ v6_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_2699])).

tff(c_2722,plain,(
    ! [B_77] :
      ( k2_lattices('#skF_8',B_77,'#skF_2'('#skF_8')) = k2_lattices('#skF_8','#skF_2'('#skF_8'),B_77)
      | ~ m1_subset_1(B_77,u1_struct_0('#skF_8'))
      | ~ v6_lattices('#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_2721])).

tff(c_2764,plain,(
    ~ v6_lattices('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_2722])).

tff(c_2767,plain,
    ( ~ v10_lattices('#skF_8')
    | v2_struct_0('#skF_8')
    | ~ l3_lattices('#skF_8') ),
    inference(resolution,[status(thm)],[c_16,c_2764])).

tff(c_2770,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_86,c_2767])).

tff(c_2772,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_2770])).

tff(c_2775,plain,(
    ! [B_607] :
      ( k2_lattices('#skF_8',B_607,'#skF_2'('#skF_8')) = k2_lattices('#skF_8','#skF_2'('#skF_8'),B_607)
      | ~ m1_subset_1(B_607,u1_struct_0('#skF_8')) ) ),
    inference(splitRight,[status(thm)],[c_2722])).

tff(c_2806,plain,(
    ! [B_82] :
      ( k2_lattices('#skF_8',k15_lattice3('#skF_8',B_82),'#skF_2'('#skF_8')) = k2_lattices('#skF_8','#skF_2'('#skF_8'),k15_lattice3('#skF_8',B_82))
      | ~ l3_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_78,c_2775])).

tff(c_2839,plain,(
    ! [B_82] :
      ( k2_lattices('#skF_8',k15_lattice3('#skF_8',B_82),'#skF_2'('#skF_8')) = k2_lattices('#skF_8','#skF_2'('#skF_8'),k15_lattice3('#skF_8',B_82))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2806])).

tff(c_2845,plain,(
    ! [B_608] : k2_lattices('#skF_8',k15_lattice3('#skF_8',B_608),'#skF_2'('#skF_8')) = k2_lattices('#skF_8','#skF_2'('#skF_8'),k15_lattice3('#skF_8',B_608)) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_2839])).

tff(c_2339,plain,(
    ! [A_81,B_82] :
      ( k2_lattices(A_81,k15_lattice3(A_81,B_82),'#skF_2'(A_81)) = '#skF_2'(A_81)
      | ~ v13_lattices(A_81)
      | ~ l1_lattices(A_81)
      | ~ l3_lattices(A_81)
      | v2_struct_0(A_81) ) ),
    inference(resolution,[status(thm)],[c_78,c_2322])).

tff(c_2851,plain,(
    ! [B_608] :
      ( k2_lattices('#skF_8','#skF_2'('#skF_8'),k15_lattice3('#skF_8',B_608)) = '#skF_2'('#skF_8')
      | ~ v13_lattices('#skF_8')
      | ~ l1_lattices('#skF_8')
      | ~ l3_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2845,c_2339])).

tff(c_2861,plain,(
    ! [B_608] :
      ( k2_lattices('#skF_8','#skF_2'('#skF_8'),k15_lattice3('#skF_8',B_608)) = '#skF_2'('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_123,c_2279,c_2851])).

tff(c_2862,plain,(
    ! [B_608] : k2_lattices('#skF_8','#skF_2'('#skF_8'),k15_lattice3('#skF_8',B_608)) = '#skF_2'('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_2861])).

tff(c_2840,plain,(
    ! [B_82] : k2_lattices('#skF_8',k15_lattice3('#skF_8',B_82),'#skF_2'('#skF_8')) = k2_lattices('#skF_8','#skF_2'('#skF_8'),k15_lattice3('#skF_8',B_82)) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_2839])).

tff(c_2867,plain,(
    ! [B_82] : k2_lattices('#skF_8',k15_lattice3('#skF_8',B_82),'#skF_2'('#skF_8')) = '#skF_2'('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2862,c_2840])).

tff(c_3739,plain,(
    ! [A_691,B_692,D_693] :
      ( r1_lattices(A_691,k15_lattice3(A_691,B_692),D_693)
      | ~ r4_lattice3(A_691,D_693,B_692)
      | ~ m1_subset_1(D_693,u1_struct_0(A_691))
      | ~ m1_subset_1(k15_lattice3(A_691,B_692),u1_struct_0(A_691))
      | ~ v4_lattice3(A_691)
      | ~ v10_lattices(A_691)
      | ~ l3_lattices(A_691)
      | v2_struct_0(A_691) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_3743,plain,(
    ! [A_694,B_695,D_696] :
      ( r1_lattices(A_694,k15_lattice3(A_694,B_695),D_696)
      | ~ r4_lattice3(A_694,D_696,B_695)
      | ~ m1_subset_1(D_696,u1_struct_0(A_694))
      | ~ v4_lattice3(A_694)
      | ~ v10_lattices(A_694)
      | ~ l3_lattices(A_694)
      | v2_struct_0(A_694) ) ),
    inference(resolution,[status(thm)],[c_78,c_3739])).

tff(c_4490,plain,(
    ! [A_778,B_779,D_780] :
      ( k2_lattices(A_778,k15_lattice3(A_778,B_779),D_780) = k15_lattice3(A_778,B_779)
      | ~ m1_subset_1(k15_lattice3(A_778,B_779),u1_struct_0(A_778))
      | ~ v9_lattices(A_778)
      | ~ v8_lattices(A_778)
      | ~ r4_lattice3(A_778,D_780,B_779)
      | ~ m1_subset_1(D_780,u1_struct_0(A_778))
      | ~ v4_lattice3(A_778)
      | ~ v10_lattices(A_778)
      | ~ l3_lattices(A_778)
      | v2_struct_0(A_778) ) ),
    inference(resolution,[status(thm)],[c_3743,c_40])).

tff(c_4494,plain,(
    ! [A_781,B_782,D_783] :
      ( k2_lattices(A_781,k15_lattice3(A_781,B_782),D_783) = k15_lattice3(A_781,B_782)
      | ~ v9_lattices(A_781)
      | ~ v8_lattices(A_781)
      | ~ r4_lattice3(A_781,D_783,B_782)
      | ~ m1_subset_1(D_783,u1_struct_0(A_781))
      | ~ v4_lattice3(A_781)
      | ~ v10_lattices(A_781)
      | ~ l3_lattices(A_781)
      | v2_struct_0(A_781) ) ),
    inference(resolution,[status(thm)],[c_78,c_4490])).

tff(c_4498,plain,(
    ! [B_782] :
      ( k2_lattices('#skF_8',k15_lattice3('#skF_8',B_782),'#skF_2'('#skF_8')) = k15_lattice3('#skF_8',B_782)
      | ~ v9_lattices('#skF_8')
      | ~ v8_lattices('#skF_8')
      | ~ r4_lattice3('#skF_8','#skF_2'('#skF_8'),B_782)
      | ~ v4_lattice3('#skF_8')
      | ~ v10_lattices('#skF_8')
      | ~ l3_lattices('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2690,c_4494])).

tff(c_4518,plain,(
    ! [B_782] :
      ( k15_lattice3('#skF_8',B_782) = '#skF_2'('#skF_8')
      | ~ r4_lattice3('#skF_8','#skF_2'('#skF_8'),B_782)
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_86,c_84,c_3080,c_3108,c_2867,c_4498])).

tff(c_4528,plain,(
    ! [B_784] :
      ( k15_lattice3('#skF_8',B_784) = '#skF_2'('#skF_8')
      | ~ r4_lattice3('#skF_8','#skF_2'('#skF_8'),B_784) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_4518])).

tff(c_4534,plain,(
    k15_lattice3('#skF_8',k1_xboole_0) = '#skF_2'('#skF_8') ),
    inference(resolution,[status(thm)],[c_2681,c_4528])).

tff(c_4543,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2651,c_4534])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:39:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.10/2.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.10/2.89  
% 9.10/2.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.10/2.89  %$ r4_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v13_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k2_lattices > k2_zfmisc_1 > k15_lattice3 > #nlpp > u1_struct_0 > k5_lattices > k1_xboole_0 > #skF_7 > #skF_2 > #skF_4 > #skF_3 > #skF_5 > #skF_8 > #skF_1 > #skF_6
% 9.10/2.89  
% 9.10/2.89  %Foreground sorts:
% 9.10/2.89  
% 9.10/2.89  
% 9.10/2.89  %Background operators:
% 9.10/2.89  
% 9.10/2.89  
% 9.10/2.89  %Foreground operators:
% 9.10/2.89  tff(l3_lattices, type, l3_lattices: $i > $o).
% 9.10/2.89  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.10/2.89  tff('#skF_7', type, '#skF_7': $i > $i).
% 9.10/2.89  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 9.10/2.89  tff(l2_lattices, type, l2_lattices: $i > $o).
% 9.10/2.89  tff('#skF_2', type, '#skF_2': $i > $i).
% 9.10/2.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.10/2.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.10/2.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.10/2.89  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 9.10/2.89  tff(l1_lattices, type, l1_lattices: $i > $o).
% 9.10/2.89  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 9.10/2.89  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.10/2.89  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 9.10/2.89  tff(v4_lattices, type, v4_lattices: $i > $o).
% 9.10/2.89  tff(v6_lattices, type, v6_lattices: $i > $o).
% 9.10/2.89  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 9.10/2.89  tff(v9_lattices, type, v9_lattices: $i > $o).
% 9.10/2.89  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 9.10/2.89  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 9.10/2.89  tff(v5_lattices, type, v5_lattices: $i > $o).
% 9.10/2.89  tff(v10_lattices, type, v10_lattices: $i > $o).
% 9.10/2.89  tff('#skF_8', type, '#skF_8': $i).
% 9.10/2.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.10/2.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.10/2.89  tff(v13_lattices, type, v13_lattices: $i > $o).
% 9.10/2.89  tff(v8_lattices, type, v8_lattices: $i > $o).
% 9.10/2.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.10/2.89  tff(k5_lattices, type, k5_lattices: $i > $i).
% 9.10/2.89  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.10/2.89  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.10/2.89  tff('#skF_6', type, '#skF_6': $i > $i).
% 9.10/2.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.10/2.89  tff(v7_lattices, type, v7_lattices: $i > $o).
% 9.10/2.89  
% 9.10/2.91  tff(f_213, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v13_lattices(A)) & l3_lattices(A)) & (k5_lattices(A) = k15_lattice3(A, k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_lattice3)).
% 9.10/2.91  tff(f_88, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 9.10/2.91  tff(f_56, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 9.10/2.91  tff(f_192, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k15_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 9.10/2.91  tff(f_124, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v13_lattices(A) <=> (?[B]: (m1_subset_1(B, u1_struct_0(A)) & (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k2_lattices(A, B, C) = B) & (k2_lattices(A, C, B) = B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_lattices)).
% 9.10/2.91  tff(f_142, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r4_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, D, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_lattice3)).
% 9.10/2.91  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.10/2.91  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 9.10/2.91  tff(f_170, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k15_lattice3(A, B)) <=> (r4_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r4_lattice3(A, D, B) => r1_lattices(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d21_lattice3)).
% 9.10/2.91  tff(f_107, axiom, (![A]: ((((~v2_struct_0(A) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k2_lattices(A, B, C) = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_lattices)).
% 9.10/2.91  tff(f_185, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v6_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k2_lattices(A, B, C) = k2_lattices(A, C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_lattices)).
% 9.10/2.91  tff(f_82, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => m1_subset_1(k5_lattices(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_lattices)).
% 9.10/2.91  tff(f_75, axiom, (![A]: ((~v2_struct_0(A) & l1_lattices(A)) => (v13_lattices(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ((B = k5_lattices(A)) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((k2_lattices(A, B, C) = B) & (k2_lattices(A, C, B) = B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattices)).
% 9.10/2.91  tff(c_82, plain, (l3_lattices('#skF_8')), inference(cnfTransformation, [status(thm)], [f_213])).
% 9.10/2.91  tff(c_119, plain, (![A_86]: (l1_lattices(A_86) | ~l3_lattices(A_86))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.10/2.91  tff(c_123, plain, (l1_lattices('#skF_8')), inference(resolution, [status(thm)], [c_82, c_119])).
% 9.10/2.91  tff(c_88, plain, (~v2_struct_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_213])).
% 9.10/2.91  tff(c_86, plain, (v10_lattices('#skF_8')), inference(cnfTransformation, [status(thm)], [f_213])).
% 9.10/2.91  tff(c_80, plain, (k15_lattice3('#skF_8', k1_xboole_0)!=k5_lattices('#skF_8') | ~l3_lattices('#skF_8') | ~v13_lattices('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_213])).
% 9.10/2.91  tff(c_90, plain, (k15_lattice3('#skF_8', k1_xboole_0)!=k5_lattices('#skF_8') | ~v13_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_80])).
% 9.10/2.91  tff(c_91, plain, (k15_lattice3('#skF_8', k1_xboole_0)!=k5_lattices('#skF_8') | ~v13_lattices('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_88, c_90])).
% 9.10/2.91  tff(c_132, plain, (~v13_lattices('#skF_8')), inference(splitLeft, [status(thm)], [c_91])).
% 9.10/2.91  tff(c_84, plain, (v4_lattice3('#skF_8')), inference(cnfTransformation, [status(thm)], [f_213])).
% 9.10/2.91  tff(c_16, plain, (![A_5]: (v6_lattices(A_5) | ~v10_lattices(A_5) | v2_struct_0(A_5) | ~l3_lattices(A_5))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.10/2.91  tff(c_12, plain, (![A_5]: (v8_lattices(A_5) | ~v10_lattices(A_5) | v2_struct_0(A_5) | ~l3_lattices(A_5))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.10/2.91  tff(c_10, plain, (![A_5]: (v9_lattices(A_5) | ~v10_lattices(A_5) | v2_struct_0(A_5) | ~l3_lattices(A_5))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.10/2.91  tff(c_78, plain, (![A_81, B_82]: (m1_subset_1(k15_lattice3(A_81, B_82), u1_struct_0(A_81)) | ~l3_lattices(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_192])).
% 9.10/2.91  tff(c_44, plain, (![A_25, B_34]: (m1_subset_1('#skF_3'(A_25, B_34), u1_struct_0(A_25)) | v13_lattices(A_25) | ~m1_subset_1(B_34, u1_struct_0(A_25)) | ~l1_lattices(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.10/2.91  tff(c_258, plain, (![A_118, B_119, C_120]: (r2_hidden('#skF_4'(A_118, B_119, C_120), C_120) | r4_lattice3(A_118, B_119, C_120) | ~m1_subset_1(B_119, u1_struct_0(A_118)) | ~l3_lattices(A_118) | v2_struct_0(A_118))), inference(cnfTransformation, [status(thm)], [f_142])).
% 9.10/2.91  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.10/2.91  tff(c_124, plain, (![A_87, B_88]: (~r2_hidden(A_87, k2_zfmisc_1(A_87, B_88)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.10/2.91  tff(c_127, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_124])).
% 9.10/2.91  tff(c_264, plain, (![A_121, B_122]: (r4_lattice3(A_121, B_122, k1_xboole_0) | ~m1_subset_1(B_122, u1_struct_0(A_121)) | ~l3_lattices(A_121) | v2_struct_0(A_121))), inference(resolution, [status(thm)], [c_258, c_127])).
% 9.10/2.91  tff(c_283, plain, (![A_25, B_34]: (r4_lattice3(A_25, '#skF_3'(A_25, B_34), k1_xboole_0) | ~l3_lattices(A_25) | v13_lattices(A_25) | ~m1_subset_1(B_34, u1_struct_0(A_25)) | ~l1_lattices(A_25) | v2_struct_0(A_25))), inference(resolution, [status(thm)], [c_44, c_264])).
% 9.10/2.91  tff(c_883, plain, (![A_240, B_241, D_242]: (r1_lattices(A_240, k15_lattice3(A_240, B_241), D_242) | ~r4_lattice3(A_240, D_242, B_241) | ~m1_subset_1(D_242, u1_struct_0(A_240)) | ~m1_subset_1(k15_lattice3(A_240, B_241), u1_struct_0(A_240)) | ~v4_lattice3(A_240) | ~v10_lattices(A_240) | ~l3_lattices(A_240) | v2_struct_0(A_240))), inference(cnfTransformation, [status(thm)], [f_170])).
% 9.10/2.91  tff(c_887, plain, (![A_243, B_244, D_245]: (r1_lattices(A_243, k15_lattice3(A_243, B_244), D_245) | ~r4_lattice3(A_243, D_245, B_244) | ~m1_subset_1(D_245, u1_struct_0(A_243)) | ~v4_lattice3(A_243) | ~v10_lattices(A_243) | ~l3_lattices(A_243) | v2_struct_0(A_243))), inference(resolution, [status(thm)], [c_78, c_883])).
% 9.10/2.91  tff(c_40, plain, (![A_18, B_22, C_24]: (k2_lattices(A_18, B_22, C_24)=B_22 | ~r1_lattices(A_18, B_22, C_24) | ~m1_subset_1(C_24, u1_struct_0(A_18)) | ~m1_subset_1(B_22, u1_struct_0(A_18)) | ~l3_lattices(A_18) | ~v9_lattices(A_18) | ~v8_lattices(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_107])).
% 9.10/2.91  tff(c_1315, plain, (![A_319, B_320, D_321]: (k2_lattices(A_319, k15_lattice3(A_319, B_320), D_321)=k15_lattice3(A_319, B_320) | ~m1_subset_1(k15_lattice3(A_319, B_320), u1_struct_0(A_319)) | ~v9_lattices(A_319) | ~v8_lattices(A_319) | ~r4_lattice3(A_319, D_321, B_320) | ~m1_subset_1(D_321, u1_struct_0(A_319)) | ~v4_lattice3(A_319) | ~v10_lattices(A_319) | ~l3_lattices(A_319) | v2_struct_0(A_319))), inference(resolution, [status(thm)], [c_887, c_40])).
% 9.10/2.91  tff(c_1319, plain, (![A_322, B_323, D_324]: (k2_lattices(A_322, k15_lattice3(A_322, B_323), D_324)=k15_lattice3(A_322, B_323) | ~v9_lattices(A_322) | ~v8_lattices(A_322) | ~r4_lattice3(A_322, D_324, B_323) | ~m1_subset_1(D_324, u1_struct_0(A_322)) | ~v4_lattice3(A_322) | ~v10_lattices(A_322) | ~l3_lattices(A_322) | v2_struct_0(A_322))), inference(resolution, [status(thm)], [c_78, c_1315])).
% 9.10/2.91  tff(c_1341, plain, (![A_25, B_323, B_34]: (k2_lattices(A_25, k15_lattice3(A_25, B_323), '#skF_3'(A_25, B_34))=k15_lattice3(A_25, B_323) | ~v9_lattices(A_25) | ~v8_lattices(A_25) | ~r4_lattice3(A_25, '#skF_3'(A_25, B_34), B_323) | ~v4_lattice3(A_25) | ~v10_lattices(A_25) | ~l3_lattices(A_25) | v13_lattices(A_25) | ~m1_subset_1(B_34, u1_struct_0(A_25)) | ~l1_lattices(A_25) | v2_struct_0(A_25))), inference(resolution, [status(thm)], [c_44, c_1319])).
% 9.10/2.91  tff(c_1447, plain, (![A_342, B_343, B_344]: (k2_lattices(A_342, k15_lattice3(A_342, B_343), '#skF_3'(A_342, B_344))=k15_lattice3(A_342, B_343) | ~v9_lattices(A_342) | ~v8_lattices(A_342) | ~r4_lattice3(A_342, '#skF_3'(A_342, B_344), B_343) | ~v4_lattice3(A_342) | ~v10_lattices(A_342) | ~l3_lattices(A_342) | v13_lattices(A_342) | ~m1_subset_1(B_344, u1_struct_0(A_342)) | ~l1_lattices(A_342) | v2_struct_0(A_342))), inference(resolution, [status(thm)], [c_44, c_1319])).
% 9.10/2.91  tff(c_399, plain, (![A_155, C_156, B_157]: (k2_lattices(A_155, C_156, B_157)=k2_lattices(A_155, B_157, C_156) | ~m1_subset_1(C_156, u1_struct_0(A_155)) | ~m1_subset_1(B_157, u1_struct_0(A_155)) | ~v6_lattices(A_155) | ~l1_lattices(A_155) | v2_struct_0(A_155))), inference(cnfTransformation, [status(thm)], [f_185])).
% 9.10/2.91  tff(c_948, plain, (![A_261, B_262, B_263]: (k2_lattices(A_261, B_262, '#skF_3'(A_261, B_263))=k2_lattices(A_261, '#skF_3'(A_261, B_263), B_262) | ~m1_subset_1(B_262, u1_struct_0(A_261)) | ~v6_lattices(A_261) | v13_lattices(A_261) | ~m1_subset_1(B_263, u1_struct_0(A_261)) | ~l1_lattices(A_261) | v2_struct_0(A_261))), inference(resolution, [status(thm)], [c_44, c_399])).
% 9.10/2.91  tff(c_974, plain, (![A_81, B_82, B_263]: (k2_lattices(A_81, k15_lattice3(A_81, B_82), '#skF_3'(A_81, B_263))=k2_lattices(A_81, '#skF_3'(A_81, B_263), k15_lattice3(A_81, B_82)) | ~v6_lattices(A_81) | v13_lattices(A_81) | ~m1_subset_1(B_263, u1_struct_0(A_81)) | ~l1_lattices(A_81) | ~l3_lattices(A_81) | v2_struct_0(A_81))), inference(resolution, [status(thm)], [c_78, c_948])).
% 9.10/2.91  tff(c_2217, plain, (![A_513, B_514, B_515]: (k2_lattices(A_513, '#skF_3'(A_513, B_514), k15_lattice3(A_513, B_515))=k15_lattice3(A_513, B_515) | ~v6_lattices(A_513) | v13_lattices(A_513) | ~m1_subset_1(B_514, u1_struct_0(A_513)) | ~l1_lattices(A_513) | ~l3_lattices(A_513) | v2_struct_0(A_513) | ~v9_lattices(A_513) | ~v8_lattices(A_513) | ~r4_lattice3(A_513, '#skF_3'(A_513, B_514), B_515) | ~v4_lattice3(A_513) | ~v10_lattices(A_513) | ~l3_lattices(A_513) | v13_lattices(A_513) | ~m1_subset_1(B_514, u1_struct_0(A_513)) | ~l1_lattices(A_513) | v2_struct_0(A_513))), inference(superposition, [status(thm), theory('equality')], [c_1447, c_974])).
% 9.10/2.91  tff(c_42, plain, (![A_25, B_34]: (k2_lattices(A_25, '#skF_3'(A_25, B_34), B_34)!=B_34 | k2_lattices(A_25, B_34, '#skF_3'(A_25, B_34))!=B_34 | v13_lattices(A_25) | ~m1_subset_1(B_34, u1_struct_0(A_25)) | ~l1_lattices(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.10/2.91  tff(c_2236, plain, (![A_516, B_517]: (k2_lattices(A_516, k15_lattice3(A_516, B_517), '#skF_3'(A_516, k15_lattice3(A_516, B_517)))!=k15_lattice3(A_516, B_517) | ~v6_lattices(A_516) | ~v9_lattices(A_516) | ~v8_lattices(A_516) | ~r4_lattice3(A_516, '#skF_3'(A_516, k15_lattice3(A_516, B_517)), B_517) | ~v4_lattice3(A_516) | ~v10_lattices(A_516) | ~l3_lattices(A_516) | v13_lattices(A_516) | ~m1_subset_1(k15_lattice3(A_516, B_517), u1_struct_0(A_516)) | ~l1_lattices(A_516) | v2_struct_0(A_516))), inference(superposition, [status(thm), theory('equality')], [c_2217, c_42])).
% 9.10/2.91  tff(c_2242, plain, (![A_518, B_519]: (~v6_lattices(A_518) | ~v9_lattices(A_518) | ~v8_lattices(A_518) | ~r4_lattice3(A_518, '#skF_3'(A_518, k15_lattice3(A_518, B_519)), B_519) | ~v4_lattice3(A_518) | ~v10_lattices(A_518) | ~l3_lattices(A_518) | v13_lattices(A_518) | ~m1_subset_1(k15_lattice3(A_518, B_519), u1_struct_0(A_518)) | ~l1_lattices(A_518) | v2_struct_0(A_518))), inference(superposition, [status(thm), theory('equality')], [c_1341, c_2236])).
% 9.10/2.91  tff(c_2248, plain, (![A_520]: (~v6_lattices(A_520) | ~v9_lattices(A_520) | ~v8_lattices(A_520) | ~v4_lattice3(A_520) | ~v10_lattices(A_520) | ~l3_lattices(A_520) | v13_lattices(A_520) | ~m1_subset_1(k15_lattice3(A_520, k1_xboole_0), u1_struct_0(A_520)) | ~l1_lattices(A_520) | v2_struct_0(A_520))), inference(resolution, [status(thm)], [c_283, c_2242])).
% 9.10/2.91  tff(c_2254, plain, (![A_521]: (~v6_lattices(A_521) | ~v9_lattices(A_521) | ~v8_lattices(A_521) | ~v4_lattice3(A_521) | ~v10_lattices(A_521) | v13_lattices(A_521) | ~l1_lattices(A_521) | ~l3_lattices(A_521) | v2_struct_0(A_521))), inference(resolution, [status(thm)], [c_78, c_2248])).
% 9.10/2.91  tff(c_2259, plain, (![A_522]: (~v6_lattices(A_522) | ~v8_lattices(A_522) | ~v4_lattice3(A_522) | v13_lattices(A_522) | ~l1_lattices(A_522) | ~v10_lattices(A_522) | v2_struct_0(A_522) | ~l3_lattices(A_522))), inference(resolution, [status(thm)], [c_10, c_2254])).
% 9.10/2.91  tff(c_2264, plain, (![A_523]: (~v6_lattices(A_523) | ~v4_lattice3(A_523) | v13_lattices(A_523) | ~l1_lattices(A_523) | ~v10_lattices(A_523) | v2_struct_0(A_523) | ~l3_lattices(A_523))), inference(resolution, [status(thm)], [c_12, c_2259])).
% 9.10/2.91  tff(c_2269, plain, (![A_524]: (~v4_lattice3(A_524) | v13_lattices(A_524) | ~l1_lattices(A_524) | ~v10_lattices(A_524) | v2_struct_0(A_524) | ~l3_lattices(A_524))), inference(resolution, [status(thm)], [c_16, c_2264])).
% 9.10/2.91  tff(c_2272, plain, (v13_lattices('#skF_8') | ~l1_lattices('#skF_8') | ~v10_lattices('#skF_8') | v2_struct_0('#skF_8') | ~l3_lattices('#skF_8')), inference(resolution, [status(thm)], [c_84, c_2269])).
% 9.10/2.91  tff(c_2275, plain, (v13_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_86, c_123, c_2272])).
% 9.10/2.91  tff(c_2277, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_132, c_2275])).
% 9.10/2.91  tff(c_2279, plain, (v13_lattices('#skF_8')), inference(splitRight, [status(thm)], [c_91])).
% 9.10/2.91  tff(c_32, plain, (![A_16]: (m1_subset_1(k5_lattices(A_16), u1_struct_0(A_16)) | ~l1_lattices(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.10/2.91  tff(c_46, plain, (![A_25]: (m1_subset_1('#skF_2'(A_25), u1_struct_0(A_25)) | ~v13_lattices(A_25) | ~l1_lattices(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.10/2.91  tff(c_2556, plain, (![A_593, C_594]: (k2_lattices(A_593, k5_lattices(A_593), C_594)=k5_lattices(A_593) | ~m1_subset_1(C_594, u1_struct_0(A_593)) | ~m1_subset_1(k5_lattices(A_593), u1_struct_0(A_593)) | ~v13_lattices(A_593) | ~l1_lattices(A_593) | v2_struct_0(A_593))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.10/2.91  tff(c_2581, plain, (![A_595]: (k2_lattices(A_595, k5_lattices(A_595), '#skF_2'(A_595))=k5_lattices(A_595) | ~m1_subset_1(k5_lattices(A_595), u1_struct_0(A_595)) | ~v13_lattices(A_595) | ~l1_lattices(A_595) | v2_struct_0(A_595))), inference(resolution, [status(thm)], [c_46, c_2556])).
% 9.10/2.91  tff(c_2585, plain, (![A_596]: (k2_lattices(A_596, k5_lattices(A_596), '#skF_2'(A_596))=k5_lattices(A_596) | ~v13_lattices(A_596) | ~l1_lattices(A_596) | v2_struct_0(A_596))), inference(resolution, [status(thm)], [c_32, c_2581])).
% 9.10/2.91  tff(c_2322, plain, (![A_543, C_544]: (k2_lattices(A_543, C_544, '#skF_2'(A_543))='#skF_2'(A_543) | ~m1_subset_1(C_544, u1_struct_0(A_543)) | ~v13_lattices(A_543) | ~l1_lattices(A_543) | v2_struct_0(A_543))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.10/2.91  tff(c_2340, plain, (![A_16]: (k2_lattices(A_16, k5_lattices(A_16), '#skF_2'(A_16))='#skF_2'(A_16) | ~v13_lattices(A_16) | ~l1_lattices(A_16) | v2_struct_0(A_16))), inference(resolution, [status(thm)], [c_32, c_2322])).
% 9.10/2.91  tff(c_2594, plain, (![A_596]: (k5_lattices(A_596)='#skF_2'(A_596) | ~v13_lattices(A_596) | ~l1_lattices(A_596) | v2_struct_0(A_596) | ~v13_lattices(A_596) | ~l1_lattices(A_596) | v2_struct_0(A_596))), inference(superposition, [status(thm), theory('equality')], [c_2585, c_2340])).
% 9.10/2.91  tff(c_2644, plain, (![A_600]: (k5_lattices(A_600)='#skF_2'(A_600) | ~v13_lattices(A_600) | ~l1_lattices(A_600) | v2_struct_0(A_600))), inference(factorization, [status(thm), theory('equality')], [c_2594])).
% 9.10/2.91  tff(c_2647, plain, (k5_lattices('#skF_8')='#skF_2'('#skF_8') | ~v13_lattices('#skF_8') | ~l1_lattices('#skF_8')), inference(resolution, [status(thm)], [c_2644, c_88])).
% 9.10/2.91  tff(c_2650, plain, (k5_lattices('#skF_8')='#skF_2'('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_2279, c_2647])).
% 9.10/2.91  tff(c_2278, plain, (k15_lattice3('#skF_8', k1_xboole_0)!=k5_lattices('#skF_8')), inference(splitRight, [status(thm)], [c_91])).
% 9.10/2.91  tff(c_2651, plain, (k15_lattice3('#skF_8', k1_xboole_0)!='#skF_2'('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2650, c_2278])).
% 9.10/2.91  tff(c_2405, plain, (![A_553, B_554, C_555]: (r2_hidden('#skF_4'(A_553, B_554, C_555), C_555) | r4_lattice3(A_553, B_554, C_555) | ~m1_subset_1(B_554, u1_struct_0(A_553)) | ~l3_lattices(A_553) | v2_struct_0(A_553))), inference(cnfTransformation, [status(thm)], [f_142])).
% 9.10/2.91  tff(c_2411, plain, (![A_556, B_557]: (r4_lattice3(A_556, B_557, k1_xboole_0) | ~m1_subset_1(B_557, u1_struct_0(A_556)) | ~l3_lattices(A_556) | v2_struct_0(A_556))), inference(resolution, [status(thm)], [c_2405, c_127])).
% 9.10/2.91  tff(c_2435, plain, (![A_16]: (r4_lattice3(A_16, k5_lattices(A_16), k1_xboole_0) | ~l3_lattices(A_16) | ~l1_lattices(A_16) | v2_struct_0(A_16))), inference(resolution, [status(thm)], [c_32, c_2411])).
% 9.10/2.91  tff(c_2661, plain, (r4_lattice3('#skF_8', '#skF_2'('#skF_8'), k1_xboole_0) | ~l3_lattices('#skF_8') | ~l1_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_2650, c_2435])).
% 9.10/2.91  tff(c_2680, plain, (r4_lattice3('#skF_8', '#skF_2'('#skF_8'), k1_xboole_0) | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_82, c_2661])).
% 9.10/2.91  tff(c_2681, plain, (r4_lattice3('#skF_8', '#skF_2'('#skF_8'), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_88, c_2680])).
% 9.10/2.91  tff(c_2670, plain, (m1_subset_1('#skF_2'('#skF_8'), u1_struct_0('#skF_8')) | ~l1_lattices('#skF_8') | v2_struct_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_2650, c_32])).
% 9.10/2.91  tff(c_2689, plain, (m1_subset_1('#skF_2'('#skF_8'), u1_struct_0('#skF_8')) | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_2670])).
% 9.10/2.91  tff(c_2690, plain, (m1_subset_1('#skF_2'('#skF_8'), u1_struct_0('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_88, c_2689])).
% 9.10/2.91  tff(c_3039, plain, (![A_623, B_624, C_625]: (r1_lattices(A_623, B_624, C_625) | k2_lattices(A_623, B_624, C_625)!=B_624 | ~m1_subset_1(C_625, u1_struct_0(A_623)) | ~m1_subset_1(B_624, u1_struct_0(A_623)) | ~l3_lattices(A_623) | ~v9_lattices(A_623) | ~v8_lattices(A_623) | v2_struct_0(A_623))), inference(cnfTransformation, [status(thm)], [f_107])).
% 9.10/2.91  tff(c_3041, plain, (![B_624]: (r1_lattices('#skF_8', B_624, '#skF_2'('#skF_8')) | k2_lattices('#skF_8', B_624, '#skF_2'('#skF_8'))!=B_624 | ~m1_subset_1(B_624, u1_struct_0('#skF_8')) | ~l3_lattices('#skF_8') | ~v9_lattices('#skF_8') | ~v8_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_2690, c_3039])).
% 9.10/2.91  tff(c_3060, plain, (![B_624]: (r1_lattices('#skF_8', B_624, '#skF_2'('#skF_8')) | k2_lattices('#skF_8', B_624, '#skF_2'('#skF_8'))!=B_624 | ~m1_subset_1(B_624, u1_struct_0('#skF_8')) | ~v9_lattices('#skF_8') | ~v8_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_3041])).
% 9.10/2.91  tff(c_3061, plain, (![B_624]: (r1_lattices('#skF_8', B_624, '#skF_2'('#skF_8')) | k2_lattices('#skF_8', B_624, '#skF_2'('#skF_8'))!=B_624 | ~m1_subset_1(B_624, u1_struct_0('#skF_8')) | ~v9_lattices('#skF_8') | ~v8_lattices('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_88, c_3060])).
% 9.10/2.91  tff(c_3070, plain, (~v8_lattices('#skF_8')), inference(splitLeft, [status(thm)], [c_3061])).
% 9.10/2.91  tff(c_3073, plain, (~v10_lattices('#skF_8') | v2_struct_0('#skF_8') | ~l3_lattices('#skF_8')), inference(resolution, [status(thm)], [c_12, c_3070])).
% 9.10/2.91  tff(c_3076, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_86, c_3073])).
% 9.10/2.91  tff(c_3078, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_3076])).
% 9.10/2.91  tff(c_3080, plain, (v8_lattices('#skF_8')), inference(splitRight, [status(thm)], [c_3061])).
% 9.10/2.91  tff(c_3079, plain, (![B_624]: (~v9_lattices('#skF_8') | r1_lattices('#skF_8', B_624, '#skF_2'('#skF_8')) | k2_lattices('#skF_8', B_624, '#skF_2'('#skF_8'))!=B_624 | ~m1_subset_1(B_624, u1_struct_0('#skF_8')))), inference(splitRight, [status(thm)], [c_3061])).
% 9.10/2.91  tff(c_3098, plain, (~v9_lattices('#skF_8')), inference(splitLeft, [status(thm)], [c_3079])).
% 9.10/2.91  tff(c_3101, plain, (~v10_lattices('#skF_8') | v2_struct_0('#skF_8') | ~l3_lattices('#skF_8')), inference(resolution, [status(thm)], [c_10, c_3098])).
% 9.10/2.91  tff(c_3104, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_86, c_3101])).
% 9.10/2.91  tff(c_3106, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_3104])).
% 9.10/2.91  tff(c_3108, plain, (v9_lattices('#skF_8')), inference(splitRight, [status(thm)], [c_3079])).
% 9.10/2.91  tff(c_70, plain, (![A_70, C_79, B_77]: (k2_lattices(A_70, C_79, B_77)=k2_lattices(A_70, B_77, C_79) | ~m1_subset_1(C_79, u1_struct_0(A_70)) | ~m1_subset_1(B_77, u1_struct_0(A_70)) | ~v6_lattices(A_70) | ~l1_lattices(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_185])).
% 9.10/2.91  tff(c_2699, plain, (![B_77]: (k2_lattices('#skF_8', B_77, '#skF_2'('#skF_8'))=k2_lattices('#skF_8', '#skF_2'('#skF_8'), B_77) | ~m1_subset_1(B_77, u1_struct_0('#skF_8')) | ~v6_lattices('#skF_8') | ~l1_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_2690, c_70])).
% 9.10/2.91  tff(c_2721, plain, (![B_77]: (k2_lattices('#skF_8', B_77, '#skF_2'('#skF_8'))=k2_lattices('#skF_8', '#skF_2'('#skF_8'), B_77) | ~m1_subset_1(B_77, u1_struct_0('#skF_8')) | ~v6_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_2699])).
% 9.10/2.91  tff(c_2722, plain, (![B_77]: (k2_lattices('#skF_8', B_77, '#skF_2'('#skF_8'))=k2_lattices('#skF_8', '#skF_2'('#skF_8'), B_77) | ~m1_subset_1(B_77, u1_struct_0('#skF_8')) | ~v6_lattices('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_88, c_2721])).
% 9.10/2.91  tff(c_2764, plain, (~v6_lattices('#skF_8')), inference(splitLeft, [status(thm)], [c_2722])).
% 9.10/2.91  tff(c_2767, plain, (~v10_lattices('#skF_8') | v2_struct_0('#skF_8') | ~l3_lattices('#skF_8')), inference(resolution, [status(thm)], [c_16, c_2764])).
% 9.10/2.91  tff(c_2770, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_86, c_2767])).
% 9.10/2.91  tff(c_2772, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_2770])).
% 9.10/2.91  tff(c_2775, plain, (![B_607]: (k2_lattices('#skF_8', B_607, '#skF_2'('#skF_8'))=k2_lattices('#skF_8', '#skF_2'('#skF_8'), B_607) | ~m1_subset_1(B_607, u1_struct_0('#skF_8')))), inference(splitRight, [status(thm)], [c_2722])).
% 9.10/2.91  tff(c_2806, plain, (![B_82]: (k2_lattices('#skF_8', k15_lattice3('#skF_8', B_82), '#skF_2'('#skF_8'))=k2_lattices('#skF_8', '#skF_2'('#skF_8'), k15_lattice3('#skF_8', B_82)) | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_78, c_2775])).
% 9.10/2.91  tff(c_2839, plain, (![B_82]: (k2_lattices('#skF_8', k15_lattice3('#skF_8', B_82), '#skF_2'('#skF_8'))=k2_lattices('#skF_8', '#skF_2'('#skF_8'), k15_lattice3('#skF_8', B_82)) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_2806])).
% 9.10/2.91  tff(c_2845, plain, (![B_608]: (k2_lattices('#skF_8', k15_lattice3('#skF_8', B_608), '#skF_2'('#skF_8'))=k2_lattices('#skF_8', '#skF_2'('#skF_8'), k15_lattice3('#skF_8', B_608)))), inference(negUnitSimplification, [status(thm)], [c_88, c_2839])).
% 9.10/2.91  tff(c_2339, plain, (![A_81, B_82]: (k2_lattices(A_81, k15_lattice3(A_81, B_82), '#skF_2'(A_81))='#skF_2'(A_81) | ~v13_lattices(A_81) | ~l1_lattices(A_81) | ~l3_lattices(A_81) | v2_struct_0(A_81))), inference(resolution, [status(thm)], [c_78, c_2322])).
% 9.10/2.91  tff(c_2851, plain, (![B_608]: (k2_lattices('#skF_8', '#skF_2'('#skF_8'), k15_lattice3('#skF_8', B_608))='#skF_2'('#skF_8') | ~v13_lattices('#skF_8') | ~l1_lattices('#skF_8') | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2845, c_2339])).
% 9.10/2.91  tff(c_2861, plain, (![B_608]: (k2_lattices('#skF_8', '#skF_2'('#skF_8'), k15_lattice3('#skF_8', B_608))='#skF_2'('#skF_8') | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_123, c_2279, c_2851])).
% 9.10/2.91  tff(c_2862, plain, (![B_608]: (k2_lattices('#skF_8', '#skF_2'('#skF_8'), k15_lattice3('#skF_8', B_608))='#skF_2'('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_88, c_2861])).
% 9.10/2.91  tff(c_2840, plain, (![B_82]: (k2_lattices('#skF_8', k15_lattice3('#skF_8', B_82), '#skF_2'('#skF_8'))=k2_lattices('#skF_8', '#skF_2'('#skF_8'), k15_lattice3('#skF_8', B_82)))), inference(negUnitSimplification, [status(thm)], [c_88, c_2839])).
% 9.10/2.91  tff(c_2867, plain, (![B_82]: (k2_lattices('#skF_8', k15_lattice3('#skF_8', B_82), '#skF_2'('#skF_8'))='#skF_2'('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2862, c_2840])).
% 9.10/2.91  tff(c_3739, plain, (![A_691, B_692, D_693]: (r1_lattices(A_691, k15_lattice3(A_691, B_692), D_693) | ~r4_lattice3(A_691, D_693, B_692) | ~m1_subset_1(D_693, u1_struct_0(A_691)) | ~m1_subset_1(k15_lattice3(A_691, B_692), u1_struct_0(A_691)) | ~v4_lattice3(A_691) | ~v10_lattices(A_691) | ~l3_lattices(A_691) | v2_struct_0(A_691))), inference(cnfTransformation, [status(thm)], [f_170])).
% 9.10/2.91  tff(c_3743, plain, (![A_694, B_695, D_696]: (r1_lattices(A_694, k15_lattice3(A_694, B_695), D_696) | ~r4_lattice3(A_694, D_696, B_695) | ~m1_subset_1(D_696, u1_struct_0(A_694)) | ~v4_lattice3(A_694) | ~v10_lattices(A_694) | ~l3_lattices(A_694) | v2_struct_0(A_694))), inference(resolution, [status(thm)], [c_78, c_3739])).
% 9.10/2.91  tff(c_4490, plain, (![A_778, B_779, D_780]: (k2_lattices(A_778, k15_lattice3(A_778, B_779), D_780)=k15_lattice3(A_778, B_779) | ~m1_subset_1(k15_lattice3(A_778, B_779), u1_struct_0(A_778)) | ~v9_lattices(A_778) | ~v8_lattices(A_778) | ~r4_lattice3(A_778, D_780, B_779) | ~m1_subset_1(D_780, u1_struct_0(A_778)) | ~v4_lattice3(A_778) | ~v10_lattices(A_778) | ~l3_lattices(A_778) | v2_struct_0(A_778))), inference(resolution, [status(thm)], [c_3743, c_40])).
% 9.10/2.91  tff(c_4494, plain, (![A_781, B_782, D_783]: (k2_lattices(A_781, k15_lattice3(A_781, B_782), D_783)=k15_lattice3(A_781, B_782) | ~v9_lattices(A_781) | ~v8_lattices(A_781) | ~r4_lattice3(A_781, D_783, B_782) | ~m1_subset_1(D_783, u1_struct_0(A_781)) | ~v4_lattice3(A_781) | ~v10_lattices(A_781) | ~l3_lattices(A_781) | v2_struct_0(A_781))), inference(resolution, [status(thm)], [c_78, c_4490])).
% 9.10/2.91  tff(c_4498, plain, (![B_782]: (k2_lattices('#skF_8', k15_lattice3('#skF_8', B_782), '#skF_2'('#skF_8'))=k15_lattice3('#skF_8', B_782) | ~v9_lattices('#skF_8') | ~v8_lattices('#skF_8') | ~r4_lattice3('#skF_8', '#skF_2'('#skF_8'), B_782) | ~v4_lattice3('#skF_8') | ~v10_lattices('#skF_8') | ~l3_lattices('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_2690, c_4494])).
% 9.10/2.91  tff(c_4518, plain, (![B_782]: (k15_lattice3('#skF_8', B_782)='#skF_2'('#skF_8') | ~r4_lattice3('#skF_8', '#skF_2'('#skF_8'), B_782) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_86, c_84, c_3080, c_3108, c_2867, c_4498])).
% 9.10/2.91  tff(c_4528, plain, (![B_784]: (k15_lattice3('#skF_8', B_784)='#skF_2'('#skF_8') | ~r4_lattice3('#skF_8', '#skF_2'('#skF_8'), B_784))), inference(negUnitSimplification, [status(thm)], [c_88, c_4518])).
% 9.10/2.91  tff(c_4534, plain, (k15_lattice3('#skF_8', k1_xboole_0)='#skF_2'('#skF_8')), inference(resolution, [status(thm)], [c_2681, c_4528])).
% 9.10/2.91  tff(c_4543, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2651, c_4534])).
% 9.10/2.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.10/2.91  
% 9.10/2.91  Inference rules
% 9.10/2.91  ----------------------
% 9.10/2.91  #Ref     : 0
% 9.10/2.91  #Sup     : 1036
% 9.10/2.91  #Fact    : 4
% 9.10/2.91  #Define  : 0
% 9.10/2.91  #Split   : 4
% 9.10/2.92  #Chain   : 0
% 9.10/2.92  #Close   : 0
% 9.10/2.92  
% 9.10/2.92  Ordering : KBO
% 9.10/2.92  
% 9.10/2.92  Simplification rules
% 9.10/2.92  ----------------------
% 9.10/2.92  #Subsume      : 234
% 9.10/2.92  #Demod        : 501
% 9.10/2.92  #Tautology    : 508
% 9.10/2.92  #SimpNegUnit  : 128
% 9.10/2.92  #BackRed      : 2
% 9.10/2.92  
% 9.10/2.92  #Partial instantiations: 0
% 9.10/2.92  #Strategies tried      : 1
% 9.10/2.92  
% 9.10/2.92  Timing (in seconds)
% 9.10/2.92  ----------------------
% 9.10/2.92  Preprocessing        : 0.36
% 9.10/2.92  Parsing              : 0.18
% 9.10/2.92  CNF conversion       : 0.03
% 9.10/2.92  Main loop            : 1.84
% 9.10/2.92  Inferencing          : 0.81
% 9.10/2.92  Reduction            : 0.36
% 9.10/2.92  Demodulation         : 0.23
% 9.10/2.92  BG Simplification    : 0.08
% 9.10/2.92  Subsumption          : 0.49
% 9.10/2.92  Abstraction          : 0.08
% 9.10/2.92  MUC search           : 0.00
% 9.10/2.92  Cooper               : 0.00
% 9.10/2.92  Total                : 2.24
% 9.10/2.92  Index Insertion      : 0.00
% 9.10/2.92  Index Deletion       : 0.00
% 9.10/2.92  Index Matching       : 0.00
% 9.10/2.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
