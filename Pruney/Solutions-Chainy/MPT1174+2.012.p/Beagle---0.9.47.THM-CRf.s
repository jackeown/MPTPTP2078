%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:54 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 725 expanded)
%              Number of leaves         :   37 ( 304 expanded)
%              Depth                    :   31
%              Number of atoms          :  388 (3974 expanded)
%              Number of equality atoms :   41 ( 543 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_orders_2 > r1_orders_2 > m2_orders_2 > v6_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k1_orders_1,type,(
    k1_orders_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_197,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_orders_1(C,k1_orders_1(u1_struct_0(A)))
               => ! [D] :
                    ( m2_orders_2(D,A,C)
                   => ( B = k1_funct_1(C,u1_struct_0(A))
                     => k3_orders_2(A,D,B) = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_orders_2)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ! [C] :
          ( m2_orders_2(C,A,B)
         => ( v6_orders_2(C,A)
            & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).

tff(f_50,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_mcart_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k3_orders_2(A,B,C),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_143,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( r2_hidden(B,k3_orders_2(A,D,C))
                  <=> ( r2_orders_2(A,B,C)
                      & r2_hidden(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

tff(f_172,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_orders_1(D,k1_orders_1(u1_struct_0(A)))
                 => ! [E] :
                      ( m2_orders_2(E,A,D)
                     => ( ( r2_hidden(B,E)
                          & C = k1_funct_1(D,u1_struct_0(A)) )
                       => r3_orders_2(A,C,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_orders_2)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_117,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ~ ( r1_orders_2(A,B,C)
                  & r2_orders_2(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_orders_2)).

tff(c_28,plain,(
    k3_orders_2('#skF_2','#skF_5','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_44,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_42,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_40,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_38,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_34,plain,(
    m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_32,plain,(
    m2_orders_2('#skF_5','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_90,plain,(
    ! [C_125,A_126,B_127] :
      ( m1_subset_1(C_125,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ m2_orders_2(C_125,A_126,B_127)
      | ~ m1_orders_1(B_127,k1_orders_1(u1_struct_0(A_126)))
      | ~ l1_orders_2(A_126)
      | ~ v5_orders_2(A_126)
      | ~ v4_orders_2(A_126)
      | ~ v3_orders_2(A_126)
      | v2_struct_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_92,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_90])).

tff(c_95,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_34,c_92])).

tff(c_96,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_95])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_6,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_1'(A_4),A_4)
      | k1_xboole_0 = A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_100,plain,(
    ! [A_128,B_129,C_130] :
      ( m1_subset_1(k3_orders_2(A_128,B_129,C_130),k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ m1_subset_1(C_130,u1_struct_0(A_128))
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_orders_2(A_128)
      | ~ v5_orders_2(A_128)
      | ~ v4_orders_2(A_128)
      | ~ v3_orders_2(A_128)
      | v2_struct_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( m1_subset_1(A_1,C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_150,plain,(
    ! [A_141,A_142,B_143,C_144] :
      ( m1_subset_1(A_141,u1_struct_0(A_142))
      | ~ r2_hidden(A_141,k3_orders_2(A_142,B_143,C_144))
      | ~ m1_subset_1(C_144,u1_struct_0(A_142))
      | ~ m1_subset_1(B_143,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ l1_orders_2(A_142)
      | ~ v5_orders_2(A_142)
      | ~ v4_orders_2(A_142)
      | ~ v3_orders_2(A_142)
      | v2_struct_0(A_142) ) ),
    inference(resolution,[status(thm)],[c_100,c_2])).

tff(c_154,plain,(
    ! [A_142,B_143,C_144] :
      ( m1_subset_1('#skF_1'(k3_orders_2(A_142,B_143,C_144)),u1_struct_0(A_142))
      | ~ m1_subset_1(C_144,u1_struct_0(A_142))
      | ~ m1_subset_1(B_143,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ l1_orders_2(A_142)
      | ~ v5_orders_2(A_142)
      | ~ v4_orders_2(A_142)
      | ~ v3_orders_2(A_142)
      | v2_struct_0(A_142)
      | k3_orders_2(A_142,B_143,C_144) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_150])).

tff(c_155,plain,(
    ! [B_145,D_146,A_147,C_148] :
      ( r2_hidden(B_145,D_146)
      | ~ r2_hidden(B_145,k3_orders_2(A_147,D_146,C_148))
      | ~ m1_subset_1(D_146,k1_zfmisc_1(u1_struct_0(A_147)))
      | ~ m1_subset_1(C_148,u1_struct_0(A_147))
      | ~ m1_subset_1(B_145,u1_struct_0(A_147))
      | ~ l1_orders_2(A_147)
      | ~ v5_orders_2(A_147)
      | ~ v4_orders_2(A_147)
      | ~ v3_orders_2(A_147)
      | v2_struct_0(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_227,plain,(
    ! [A_167,D_168,C_169] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_167,D_168,C_169)),D_168)
      | ~ m1_subset_1(D_168,k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ m1_subset_1(C_169,u1_struct_0(A_167))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_167,D_168,C_169)),u1_struct_0(A_167))
      | ~ l1_orders_2(A_167)
      | ~ v5_orders_2(A_167)
      | ~ v4_orders_2(A_167)
      | ~ v3_orders_2(A_167)
      | v2_struct_0(A_167)
      | k3_orders_2(A_167,D_168,C_169) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_155])).

tff(c_239,plain,(
    ! [A_172,B_173,C_174] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_172,B_173,C_174)),B_173)
      | ~ m1_subset_1(C_174,u1_struct_0(A_172))
      | ~ m1_subset_1(B_173,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ l1_orders_2(A_172)
      | ~ v5_orders_2(A_172)
      | ~ v4_orders_2(A_172)
      | ~ v3_orders_2(A_172)
      | v2_struct_0(A_172)
      | k3_orders_2(A_172,B_173,C_174) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_154,c_227])).

tff(c_99,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_1,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_96,c_2])).

tff(c_232,plain,(
    ! [D_168,C_169] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_168,C_169)),D_168)
      | ~ m1_subset_1(D_168,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_169,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_168,C_169) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_168,C_169)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_99,c_227])).

tff(c_236,plain,(
    ! [D_168,C_169] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_168,C_169)),D_168)
      | ~ m1_subset_1(D_168,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_169,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_168,C_169) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_168,C_169)),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_232])).

tff(c_237,plain,(
    ! [D_168,C_169] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_168,C_169)),D_168)
      | ~ m1_subset_1(D_168,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_169,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_168,C_169) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_168,C_169)),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_236])).

tff(c_242,plain,(
    ! [C_174] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_174)),'#skF_5')
      | ~ m1_subset_1(C_174,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_174) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_239,c_237])).

tff(c_267,plain,(
    ! [C_174] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_174)),'#skF_5')
      | ~ m1_subset_1(C_174,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_174) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_96,c_242])).

tff(c_268,plain,(
    ! [C_174] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_174)),'#skF_5')
      | ~ m1_subset_1(C_174,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_174) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_267])).

tff(c_30,plain,(
    k1_funct_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_282,plain,(
    ! [A_176,D_177,B_178,E_179] :
      ( r3_orders_2(A_176,k1_funct_1(D_177,u1_struct_0(A_176)),B_178)
      | ~ r2_hidden(B_178,E_179)
      | ~ m2_orders_2(E_179,A_176,D_177)
      | ~ m1_orders_1(D_177,k1_orders_1(u1_struct_0(A_176)))
      | ~ m1_subset_1(k1_funct_1(D_177,u1_struct_0(A_176)),u1_struct_0(A_176))
      | ~ m1_subset_1(B_178,u1_struct_0(A_176))
      | ~ l1_orders_2(A_176)
      | ~ v5_orders_2(A_176)
      | ~ v4_orders_2(A_176)
      | ~ v3_orders_2(A_176)
      | v2_struct_0(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_316,plain,(
    ! [A_188,D_189,C_190] :
      ( r3_orders_2(A_188,k1_funct_1(D_189,u1_struct_0(A_188)),'#skF_1'(k3_orders_2('#skF_2','#skF_5',C_190)))
      | ~ m2_orders_2('#skF_5',A_188,D_189)
      | ~ m1_orders_1(D_189,k1_orders_1(u1_struct_0(A_188)))
      | ~ m1_subset_1(k1_funct_1(D_189,u1_struct_0(A_188)),u1_struct_0(A_188))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_190)),u1_struct_0(A_188))
      | ~ l1_orders_2(A_188)
      | ~ v5_orders_2(A_188)
      | ~ v4_orders_2(A_188)
      | ~ v3_orders_2(A_188)
      | v2_struct_0(A_188)
      | ~ m1_subset_1(C_190,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_190) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_268,c_282])).

tff(c_321,plain,(
    ! [C_190] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_190)))
      | ~ m2_orders_2('#skF_5','#skF_2','#skF_4')
      | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k1_funct_1('#skF_4',u1_struct_0('#skF_2')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_190)),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_190,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_190) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_316])).

tff(c_324,plain,(
    ! [C_190] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_190)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_190)),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_190,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_190) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_30,c_34,c_32,c_321])).

tff(c_326,plain,(
    ! [C_191] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_191)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_191)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_191,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_191) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_324])).

tff(c_330,plain,(
    ! [C_144] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_144)))
      | ~ m1_subset_1(C_144,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_144) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_154,c_326])).

tff(c_336,plain,(
    ! [C_144] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_144)))
      | ~ m1_subset_1(C_144,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_144) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_96,c_330])).

tff(c_339,plain,(
    ! [C_192] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_192)))
      | ~ m1_subset_1(C_192,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_192) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_336])).

tff(c_16,plain,(
    ! [A_29,B_30,C_31] :
      ( r1_orders_2(A_29,B_30,C_31)
      | ~ r3_orders_2(A_29,B_30,C_31)
      | ~ m1_subset_1(C_31,u1_struct_0(A_29))
      | ~ m1_subset_1(B_30,u1_struct_0(A_29))
      | ~ l1_orders_2(A_29)
      | ~ v3_orders_2(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_341,plain,(
    ! [C_192] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_192)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_192)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_192,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_192) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_339,c_16])).

tff(c_344,plain,(
    ! [C_192] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_192)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_192)),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_192,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_192) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_36,c_341])).

tff(c_346,plain,(
    ! [C_193] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_193)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_193)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_193,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_193) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_344])).

tff(c_350,plain,(
    ! [C_144] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_144)))
      | ~ m1_subset_1(C_144,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_144) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_154,c_346])).

tff(c_356,plain,(
    ! [C_144] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_144)))
      | ~ m1_subset_1(C_144,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_144) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_96,c_350])).

tff(c_357,plain,(
    ! [C_144] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_144)))
      | ~ m1_subset_1(C_144,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_144) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_356])).

tff(c_160,plain,(
    ! [A_149,B_150,C_151,D_152] :
      ( r2_orders_2(A_149,B_150,C_151)
      | ~ r2_hidden(B_150,k3_orders_2(A_149,D_152,C_151))
      | ~ m1_subset_1(D_152,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ m1_subset_1(C_151,u1_struct_0(A_149))
      | ~ m1_subset_1(B_150,u1_struct_0(A_149))
      | ~ l1_orders_2(A_149)
      | ~ v5_orders_2(A_149)
      | ~ v4_orders_2(A_149)
      | ~ v3_orders_2(A_149)
      | v2_struct_0(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_295,plain,(
    ! [A_180,D_181,C_182] :
      ( r2_orders_2(A_180,'#skF_1'(k3_orders_2(A_180,D_181,C_182)),C_182)
      | ~ m1_subset_1(D_181,k1_zfmisc_1(u1_struct_0(A_180)))
      | ~ m1_subset_1(C_182,u1_struct_0(A_180))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_180,D_181,C_182)),u1_struct_0(A_180))
      | ~ l1_orders_2(A_180)
      | ~ v5_orders_2(A_180)
      | ~ v4_orders_2(A_180)
      | ~ v3_orders_2(A_180)
      | v2_struct_0(A_180)
      | k3_orders_2(A_180,D_181,C_182) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_160])).

tff(c_300,plain,(
    ! [D_181,C_182] :
      ( r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2',D_181,C_182)),C_182)
      | ~ m1_subset_1(D_181,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_182,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_181,C_182) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_181,C_182)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_99,c_295])).

tff(c_304,plain,(
    ! [D_181,C_182] :
      ( r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2',D_181,C_182)),C_182)
      | ~ m1_subset_1(D_181,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_182,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_181,C_182) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_181,C_182)),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_300])).

tff(c_306,plain,(
    ! [D_183,C_184] :
      ( r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2',D_183,C_184)),C_184)
      | ~ m1_subset_1(D_183,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_184,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_183,C_184) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_183,C_184)),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_304])).

tff(c_18,plain,(
    ! [A_32,C_38,B_36] :
      ( ~ r2_orders_2(A_32,C_38,B_36)
      | ~ r1_orders_2(A_32,B_36,C_38)
      | ~ m1_subset_1(C_38,u1_struct_0(A_32))
      | ~ m1_subset_1(B_36,u1_struct_0(A_32))
      | ~ l1_orders_2(A_32)
      | ~ v5_orders_2(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_308,plain,(
    ! [C_184,D_183] :
      ( ~ r1_orders_2('#skF_2',C_184,'#skF_1'(k3_orders_2('#skF_2',D_183,C_184)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2',D_183,C_184)),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ m1_subset_1(D_183,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_184,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_183,C_184) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_183,C_184)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_306,c_18])).

tff(c_438,plain,(
    ! [C_213,D_214] :
      ( ~ r1_orders_2('#skF_2',C_213,'#skF_1'(k3_orders_2('#skF_2',D_214,C_213)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2',D_214,C_213)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(D_214,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_213,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_214,C_213) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_214,C_213)),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_308])).

tff(c_447,plain,
    ( ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')),'#skF_5')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_357,c_438])).

tff(c_456,plain,
    ( ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')),u1_struct_0('#skF_2'))
    | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')),'#skF_5')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_96,c_447])).

tff(c_457,plain,
    ( ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')),u1_struct_0('#skF_2'))
    | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_456])).

tff(c_458,plain,(
    ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_457])).

tff(c_461,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_268,c_458])).

tff(c_467,plain,(
    k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_461])).

tff(c_469,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_467])).

tff(c_470,plain,(
    ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_457])).

tff(c_483,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_154,c_470])).

tff(c_489,plain,
    ( v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_96,c_36,c_483])).

tff(c_491,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_46,c_489])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:24:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.09/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.48  
% 3.25/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.49  %$ r3_orders_2 > r2_orders_2 > r1_orders_2 > m2_orders_2 > v6_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.25/1.49  
% 3.25/1.49  %Foreground sorts:
% 3.25/1.49  
% 3.25/1.49  
% 3.25/1.49  %Background operators:
% 3.25/1.49  
% 3.25/1.49  
% 3.25/1.49  %Foreground operators:
% 3.25/1.49  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.25/1.49  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 3.25/1.49  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.25/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.25/1.49  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.25/1.49  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.25/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.25/1.49  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 3.25/1.49  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 3.25/1.49  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 3.25/1.49  tff('#skF_5', type, '#skF_5': $i).
% 3.25/1.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.25/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.25/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.25/1.49  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.25/1.49  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.25/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.25/1.49  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.25/1.49  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.25/1.49  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 3.25/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.25/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.49  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 3.25/1.49  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 3.25/1.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.25/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.25/1.49  
% 3.25/1.51  tff(f_197, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_orders_1(C, k1_orders_1(u1_struct_0(A))) => (![D]: (m2_orders_2(D, A, C) => ((B = k1_funct_1(C, u1_struct_0(A))) => (k3_orders_2(A, D, B) = k1_xboole_0)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_orders_2)).
% 3.25/1.51  tff(f_87, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 3.25/1.51  tff(f_50, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_mcart_1)).
% 3.25/1.51  tff(f_67, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 3.25/1.51  tff(f_31, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.25/1.51  tff(f_143, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 3.25/1.51  tff(f_172, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_orders_1(D, k1_orders_1(u1_struct_0(A))) => (![E]: (m2_orders_2(E, A, D) => ((r2_hidden(B, E) & (C = k1_funct_1(D, u1_struct_0(A)))) => r3_orders_2(A, C, B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_orders_2)).
% 3.25/1.51  tff(f_102, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 3.25/1.51  tff(f_117, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r1_orders_2(A, B, C) & r2_orders_2(A, C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_orders_2)).
% 3.25/1.51  tff(c_28, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.25/1.51  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.25/1.51  tff(c_44, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.25/1.51  tff(c_42, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.25/1.51  tff(c_40, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.25/1.51  tff(c_38, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.25/1.51  tff(c_34, plain, (m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.25/1.51  tff(c_32, plain, (m2_orders_2('#skF_5', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.25/1.51  tff(c_90, plain, (![C_125, A_126, B_127]: (m1_subset_1(C_125, k1_zfmisc_1(u1_struct_0(A_126))) | ~m2_orders_2(C_125, A_126, B_127) | ~m1_orders_1(B_127, k1_orders_1(u1_struct_0(A_126))) | ~l1_orders_2(A_126) | ~v5_orders_2(A_126) | ~v4_orders_2(A_126) | ~v3_orders_2(A_126) | v2_struct_0(A_126))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.25/1.51  tff(c_92, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_90])).
% 3.25/1.51  tff(c_95, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_34, c_92])).
% 3.25/1.51  tff(c_96, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_46, c_95])).
% 3.25/1.51  tff(c_36, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.25/1.51  tff(c_6, plain, (![A_4]: (r2_hidden('#skF_1'(A_4), A_4) | k1_xboole_0=A_4)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.25/1.51  tff(c_100, plain, (![A_128, B_129, C_130]: (m1_subset_1(k3_orders_2(A_128, B_129, C_130), k1_zfmisc_1(u1_struct_0(A_128))) | ~m1_subset_1(C_130, u1_struct_0(A_128)) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_orders_2(A_128) | ~v5_orders_2(A_128) | ~v4_orders_2(A_128) | ~v3_orders_2(A_128) | v2_struct_0(A_128))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.25/1.51  tff(c_2, plain, (![A_1, C_3, B_2]: (m1_subset_1(A_1, C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.25/1.51  tff(c_150, plain, (![A_141, A_142, B_143, C_144]: (m1_subset_1(A_141, u1_struct_0(A_142)) | ~r2_hidden(A_141, k3_orders_2(A_142, B_143, C_144)) | ~m1_subset_1(C_144, u1_struct_0(A_142)) | ~m1_subset_1(B_143, k1_zfmisc_1(u1_struct_0(A_142))) | ~l1_orders_2(A_142) | ~v5_orders_2(A_142) | ~v4_orders_2(A_142) | ~v3_orders_2(A_142) | v2_struct_0(A_142))), inference(resolution, [status(thm)], [c_100, c_2])).
% 3.25/1.51  tff(c_154, plain, (![A_142, B_143, C_144]: (m1_subset_1('#skF_1'(k3_orders_2(A_142, B_143, C_144)), u1_struct_0(A_142)) | ~m1_subset_1(C_144, u1_struct_0(A_142)) | ~m1_subset_1(B_143, k1_zfmisc_1(u1_struct_0(A_142))) | ~l1_orders_2(A_142) | ~v5_orders_2(A_142) | ~v4_orders_2(A_142) | ~v3_orders_2(A_142) | v2_struct_0(A_142) | k3_orders_2(A_142, B_143, C_144)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_150])).
% 3.25/1.51  tff(c_155, plain, (![B_145, D_146, A_147, C_148]: (r2_hidden(B_145, D_146) | ~r2_hidden(B_145, k3_orders_2(A_147, D_146, C_148)) | ~m1_subset_1(D_146, k1_zfmisc_1(u1_struct_0(A_147))) | ~m1_subset_1(C_148, u1_struct_0(A_147)) | ~m1_subset_1(B_145, u1_struct_0(A_147)) | ~l1_orders_2(A_147) | ~v5_orders_2(A_147) | ~v4_orders_2(A_147) | ~v3_orders_2(A_147) | v2_struct_0(A_147))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.25/1.51  tff(c_227, plain, (![A_167, D_168, C_169]: (r2_hidden('#skF_1'(k3_orders_2(A_167, D_168, C_169)), D_168) | ~m1_subset_1(D_168, k1_zfmisc_1(u1_struct_0(A_167))) | ~m1_subset_1(C_169, u1_struct_0(A_167)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_167, D_168, C_169)), u1_struct_0(A_167)) | ~l1_orders_2(A_167) | ~v5_orders_2(A_167) | ~v4_orders_2(A_167) | ~v3_orders_2(A_167) | v2_struct_0(A_167) | k3_orders_2(A_167, D_168, C_169)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_155])).
% 3.25/1.51  tff(c_239, plain, (![A_172, B_173, C_174]: (r2_hidden('#skF_1'(k3_orders_2(A_172, B_173, C_174)), B_173) | ~m1_subset_1(C_174, u1_struct_0(A_172)) | ~m1_subset_1(B_173, k1_zfmisc_1(u1_struct_0(A_172))) | ~l1_orders_2(A_172) | ~v5_orders_2(A_172) | ~v4_orders_2(A_172) | ~v3_orders_2(A_172) | v2_struct_0(A_172) | k3_orders_2(A_172, B_173, C_174)=k1_xboole_0)), inference(resolution, [status(thm)], [c_154, c_227])).
% 3.25/1.51  tff(c_99, plain, (![A_1]: (m1_subset_1(A_1, u1_struct_0('#skF_2')) | ~r2_hidden(A_1, '#skF_5'))), inference(resolution, [status(thm)], [c_96, c_2])).
% 3.25/1.51  tff(c_232, plain, (![D_168, C_169]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_168, C_169)), D_168) | ~m1_subset_1(D_168, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_169, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_168, C_169)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_168, C_169)), '#skF_5'))), inference(resolution, [status(thm)], [c_99, c_227])).
% 3.25/1.51  tff(c_236, plain, (![D_168, C_169]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_168, C_169)), D_168) | ~m1_subset_1(D_168, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_169, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_168, C_169)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_168, C_169)), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_232])).
% 3.25/1.51  tff(c_237, plain, (![D_168, C_169]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_168, C_169)), D_168) | ~m1_subset_1(D_168, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_169, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_168, C_169)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_168, C_169)), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_46, c_236])).
% 3.25/1.51  tff(c_242, plain, (![C_174]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_174)), '#skF_5') | ~m1_subset_1(C_174, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_174)=k1_xboole_0)), inference(resolution, [status(thm)], [c_239, c_237])).
% 3.25/1.51  tff(c_267, plain, (![C_174]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_174)), '#skF_5') | ~m1_subset_1(C_174, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_174)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_96, c_242])).
% 3.25/1.51  tff(c_268, plain, (![C_174]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_174)), '#skF_5') | ~m1_subset_1(C_174, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_174)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_46, c_267])).
% 3.25/1.51  tff(c_30, plain, (k1_funct_1('#skF_4', u1_struct_0('#skF_2'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_197])).
% 3.25/1.51  tff(c_282, plain, (![A_176, D_177, B_178, E_179]: (r3_orders_2(A_176, k1_funct_1(D_177, u1_struct_0(A_176)), B_178) | ~r2_hidden(B_178, E_179) | ~m2_orders_2(E_179, A_176, D_177) | ~m1_orders_1(D_177, k1_orders_1(u1_struct_0(A_176))) | ~m1_subset_1(k1_funct_1(D_177, u1_struct_0(A_176)), u1_struct_0(A_176)) | ~m1_subset_1(B_178, u1_struct_0(A_176)) | ~l1_orders_2(A_176) | ~v5_orders_2(A_176) | ~v4_orders_2(A_176) | ~v3_orders_2(A_176) | v2_struct_0(A_176))), inference(cnfTransformation, [status(thm)], [f_172])).
% 3.25/1.51  tff(c_316, plain, (![A_188, D_189, C_190]: (r3_orders_2(A_188, k1_funct_1(D_189, u1_struct_0(A_188)), '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_190))) | ~m2_orders_2('#skF_5', A_188, D_189) | ~m1_orders_1(D_189, k1_orders_1(u1_struct_0(A_188))) | ~m1_subset_1(k1_funct_1(D_189, u1_struct_0(A_188)), u1_struct_0(A_188)) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_190)), u1_struct_0(A_188)) | ~l1_orders_2(A_188) | ~v5_orders_2(A_188) | ~v4_orders_2(A_188) | ~v3_orders_2(A_188) | v2_struct_0(A_188) | ~m1_subset_1(C_190, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_190)=k1_xboole_0)), inference(resolution, [status(thm)], [c_268, c_282])).
% 3.25/1.51  tff(c_321, plain, (![C_190]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_190))) | ~m2_orders_2('#skF_5', '#skF_2', '#skF_4') | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_funct_1('#skF_4', u1_struct_0('#skF_2')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_190)), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(C_190, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_190)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30, c_316])).
% 3.25/1.51  tff(c_324, plain, (![C_190]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_190))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_190)), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_190, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_190)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_36, c_30, c_34, c_32, c_321])).
% 3.25/1.51  tff(c_326, plain, (![C_191]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_191))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_191)), u1_struct_0('#skF_2')) | ~m1_subset_1(C_191, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_191)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_46, c_324])).
% 3.25/1.51  tff(c_330, plain, (![C_144]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_144))) | ~m1_subset_1(C_144, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_144)=k1_xboole_0)), inference(resolution, [status(thm)], [c_154, c_326])).
% 3.25/1.51  tff(c_336, plain, (![C_144]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_144))) | ~m1_subset_1(C_144, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_144)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_96, c_330])).
% 3.25/1.51  tff(c_339, plain, (![C_192]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_192))) | ~m1_subset_1(C_192, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_192)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_46, c_336])).
% 3.25/1.51  tff(c_16, plain, (![A_29, B_30, C_31]: (r1_orders_2(A_29, B_30, C_31) | ~r3_orders_2(A_29, B_30, C_31) | ~m1_subset_1(C_31, u1_struct_0(A_29)) | ~m1_subset_1(B_30, u1_struct_0(A_29)) | ~l1_orders_2(A_29) | ~v3_orders_2(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.25/1.51  tff(c_341, plain, (![C_192]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_192))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_192)), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(C_192, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_192)=k1_xboole_0)), inference(resolution, [status(thm)], [c_339, c_16])).
% 3.25/1.51  tff(c_344, plain, (![C_192]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_192))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_192)), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_192, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_192)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_36, c_341])).
% 3.25/1.51  tff(c_346, plain, (![C_193]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_193))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_193)), u1_struct_0('#skF_2')) | ~m1_subset_1(C_193, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_193)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_46, c_344])).
% 3.25/1.51  tff(c_350, plain, (![C_144]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_144))) | ~m1_subset_1(C_144, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_144)=k1_xboole_0)), inference(resolution, [status(thm)], [c_154, c_346])).
% 3.25/1.51  tff(c_356, plain, (![C_144]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_144))) | ~m1_subset_1(C_144, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_144)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_96, c_350])).
% 3.25/1.51  tff(c_357, plain, (![C_144]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_144))) | ~m1_subset_1(C_144, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_144)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_46, c_356])).
% 3.25/1.51  tff(c_160, plain, (![A_149, B_150, C_151, D_152]: (r2_orders_2(A_149, B_150, C_151) | ~r2_hidden(B_150, k3_orders_2(A_149, D_152, C_151)) | ~m1_subset_1(D_152, k1_zfmisc_1(u1_struct_0(A_149))) | ~m1_subset_1(C_151, u1_struct_0(A_149)) | ~m1_subset_1(B_150, u1_struct_0(A_149)) | ~l1_orders_2(A_149) | ~v5_orders_2(A_149) | ~v4_orders_2(A_149) | ~v3_orders_2(A_149) | v2_struct_0(A_149))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.25/1.51  tff(c_295, plain, (![A_180, D_181, C_182]: (r2_orders_2(A_180, '#skF_1'(k3_orders_2(A_180, D_181, C_182)), C_182) | ~m1_subset_1(D_181, k1_zfmisc_1(u1_struct_0(A_180))) | ~m1_subset_1(C_182, u1_struct_0(A_180)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_180, D_181, C_182)), u1_struct_0(A_180)) | ~l1_orders_2(A_180) | ~v5_orders_2(A_180) | ~v4_orders_2(A_180) | ~v3_orders_2(A_180) | v2_struct_0(A_180) | k3_orders_2(A_180, D_181, C_182)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_160])).
% 3.25/1.51  tff(c_300, plain, (![D_181, C_182]: (r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', D_181, C_182)), C_182) | ~m1_subset_1(D_181, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_182, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_181, C_182)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_181, C_182)), '#skF_5'))), inference(resolution, [status(thm)], [c_99, c_295])).
% 3.25/1.51  tff(c_304, plain, (![D_181, C_182]: (r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', D_181, C_182)), C_182) | ~m1_subset_1(D_181, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_182, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_181, C_182)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_181, C_182)), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_300])).
% 3.25/1.51  tff(c_306, plain, (![D_183, C_184]: (r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', D_183, C_184)), C_184) | ~m1_subset_1(D_183, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_184, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_183, C_184)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_183, C_184)), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_46, c_304])).
% 3.25/1.51  tff(c_18, plain, (![A_32, C_38, B_36]: (~r2_orders_2(A_32, C_38, B_36) | ~r1_orders_2(A_32, B_36, C_38) | ~m1_subset_1(C_38, u1_struct_0(A_32)) | ~m1_subset_1(B_36, u1_struct_0(A_32)) | ~l1_orders_2(A_32) | ~v5_orders_2(A_32))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.25/1.51  tff(c_308, plain, (![C_184, D_183]: (~r1_orders_2('#skF_2', C_184, '#skF_1'(k3_orders_2('#skF_2', D_183, C_184))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', D_183, C_184)), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~m1_subset_1(D_183, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_184, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_183, C_184)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_183, C_184)), '#skF_5'))), inference(resolution, [status(thm)], [c_306, c_18])).
% 3.25/1.51  tff(c_438, plain, (![C_213, D_214]: (~r1_orders_2('#skF_2', C_213, '#skF_1'(k3_orders_2('#skF_2', D_214, C_213))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', D_214, C_213)), u1_struct_0('#skF_2')) | ~m1_subset_1(D_214, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_213, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_214, C_213)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_214, C_213)), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_308])).
% 3.25/1.51  tff(c_447, plain, (~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), '#skF_5') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_357, c_438])).
% 3.25/1.51  tff(c_456, plain, (~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), u1_struct_0('#skF_2')) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), '#skF_5') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_96, c_447])).
% 3.25/1.51  tff(c_457, plain, (~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), u1_struct_0('#skF_2')) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_28, c_456])).
% 3.25/1.51  tff(c_458, plain, (~r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), '#skF_5')), inference(splitLeft, [status(thm)], [c_457])).
% 3.25/1.51  tff(c_461, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_268, c_458])).
% 3.25/1.51  tff(c_467, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_461])).
% 3.25/1.51  tff(c_469, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_467])).
% 3.25/1.51  tff(c_470, plain, (~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_457])).
% 3.25/1.51  tff(c_483, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_154, c_470])).
% 3.25/1.51  tff(c_489, plain, (v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_96, c_36, c_483])).
% 3.25/1.51  tff(c_491, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_46, c_489])).
% 3.25/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.51  
% 3.25/1.51  Inference rules
% 3.25/1.51  ----------------------
% 3.25/1.51  #Ref     : 0
% 3.25/1.51  #Sup     : 81
% 3.25/1.51  #Fact    : 0
% 3.25/1.51  #Define  : 0
% 3.25/1.51  #Split   : 2
% 3.25/1.51  #Chain   : 0
% 3.25/1.51  #Close   : 0
% 3.25/1.51  
% 3.25/1.51  Ordering : KBO
% 3.25/1.51  
% 3.25/1.51  Simplification rules
% 3.25/1.51  ----------------------
% 3.25/1.51  #Subsume      : 13
% 3.25/1.51  #Demod        : 130
% 3.25/1.51  #Tautology    : 12
% 3.25/1.51  #SimpNegUnit  : 32
% 3.25/1.51  #BackRed      : 0
% 3.25/1.51  
% 3.25/1.51  #Partial instantiations: 0
% 3.25/1.51  #Strategies tried      : 1
% 3.25/1.51  
% 3.25/1.51  Timing (in seconds)
% 3.25/1.51  ----------------------
% 3.25/1.51  Preprocessing        : 0.34
% 3.25/1.52  Parsing              : 0.18
% 3.25/1.52  CNF conversion       : 0.03
% 3.25/1.52  Main loop            : 0.39
% 3.25/1.52  Inferencing          : 0.16
% 3.25/1.52  Reduction            : 0.11
% 3.25/1.52  Demodulation         : 0.07
% 3.25/1.52  BG Simplification    : 0.02
% 3.25/1.52  Subsumption          : 0.08
% 3.25/1.52  Abstraction          : 0.02
% 3.25/1.52  MUC search           : 0.00
% 3.25/1.52  Cooper               : 0.00
% 3.25/1.52  Total                : 0.77
% 3.25/1.52  Index Insertion      : 0.00
% 3.25/1.52  Index Deletion       : 0.00
% 3.25/1.52  Index Matching       : 0.00
% 3.25/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
