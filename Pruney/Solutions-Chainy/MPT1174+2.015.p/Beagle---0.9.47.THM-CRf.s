%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:54 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 3.99s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 330 expanded)
%              Number of leaves         :   37 ( 149 expanded)
%              Depth                    :   30
%              Number of atoms          :  367 (1729 expanded)
%              Number of equality atoms :   37 ( 243 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_orders_2 > r1_orders_2 > m2_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k4_tarski > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(f_194,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_orders_2)).

tff(f_84,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k3_orders_2(A,B,C),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_orders_2)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_140,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

tff(f_169,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_orders_2)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_114,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ~ ( r1_orders_2(A,B,C)
                  & r2_orders_2(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_orders_2)).

tff(c_30,plain,(
    k3_orders_2('#skF_2','#skF_5','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_46,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_44,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_42,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_40,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_36,plain,(
    m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_34,plain,(
    m2_orders_2('#skF_5','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_87,plain,(
    ! [C_115,A_116,B_117] :
      ( m1_subset_1(C_115,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ m2_orders_2(C_115,A_116,B_117)
      | ~ m1_orders_1(B_117,k1_orders_1(u1_struct_0(A_116)))
      | ~ l1_orders_2(A_116)
      | ~ v5_orders_2(A_116)
      | ~ v4_orders_2(A_116)
      | ~ v3_orders_2(A_116)
      | v2_struct_0(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_89,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_87])).

tff(c_92,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_36,c_89])).

tff(c_93,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_92])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_4,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_1'(A_4),A_4)
      | k1_xboole_0 = A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_94,plain,(
    ! [A_118,B_119,C_120] :
      ( m1_subset_1(k3_orders_2(A_118,B_119,C_120),k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ m1_subset_1(C_120,u1_struct_0(A_118))
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_orders_2(A_118)
      | ~ v5_orders_2(A_118)
      | ~ v4_orders_2(A_118)
      | ~ v3_orders_2(A_118)
      | v2_struct_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( m1_subset_1(A_1,C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_140,plain,(
    ! [A_128,A_129,B_130,C_131] :
      ( m1_subset_1(A_128,u1_struct_0(A_129))
      | ~ r2_hidden(A_128,k3_orders_2(A_129,B_130,C_131))
      | ~ m1_subset_1(C_131,u1_struct_0(A_129))
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_orders_2(A_129)
      | ~ v5_orders_2(A_129)
      | ~ v4_orders_2(A_129)
      | ~ v3_orders_2(A_129)
      | v2_struct_0(A_129) ) ),
    inference(resolution,[status(thm)],[c_94,c_2])).

tff(c_144,plain,(
    ! [A_129,B_130,C_131] :
      ( m1_subset_1('#skF_1'(k3_orders_2(A_129,B_130,C_131)),u1_struct_0(A_129))
      | ~ m1_subset_1(C_131,u1_struct_0(A_129))
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_orders_2(A_129)
      | ~ v5_orders_2(A_129)
      | ~ v4_orders_2(A_129)
      | ~ v3_orders_2(A_129)
      | v2_struct_0(A_129)
      | k3_orders_2(A_129,B_130,C_131) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_140])).

tff(c_32,plain,(
    k1_funct_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_145,plain,(
    ! [B_132,D_133,A_134,C_135] :
      ( r2_hidden(B_132,D_133)
      | ~ r2_hidden(B_132,k3_orders_2(A_134,D_133,C_135))
      | ~ m1_subset_1(D_133,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ m1_subset_1(C_135,u1_struct_0(A_134))
      | ~ m1_subset_1(B_132,u1_struct_0(A_134))
      | ~ l1_orders_2(A_134)
      | ~ v5_orders_2(A_134)
      | ~ v4_orders_2(A_134)
      | ~ v3_orders_2(A_134)
      | v2_struct_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_225,plain,(
    ! [A_160,D_161,C_162] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_160,D_161,C_162)),D_161)
      | ~ m1_subset_1(D_161,k1_zfmisc_1(u1_struct_0(A_160)))
      | ~ m1_subset_1(C_162,u1_struct_0(A_160))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_160,D_161,C_162)),u1_struct_0(A_160))
      | ~ l1_orders_2(A_160)
      | ~ v5_orders_2(A_160)
      | ~ v4_orders_2(A_160)
      | ~ v3_orders_2(A_160)
      | v2_struct_0(A_160)
      | k3_orders_2(A_160,D_161,C_162) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_145])).

tff(c_237,plain,(
    ! [A_165,B_166,C_167] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_165,B_166,C_167)),B_166)
      | ~ m1_subset_1(C_167,u1_struct_0(A_165))
      | ~ m1_subset_1(B_166,k1_zfmisc_1(u1_struct_0(A_165)))
      | ~ l1_orders_2(A_165)
      | ~ v5_orders_2(A_165)
      | ~ v4_orders_2(A_165)
      | ~ v3_orders_2(A_165)
      | v2_struct_0(A_165)
      | k3_orders_2(A_165,B_166,C_167) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_144,c_225])).

tff(c_100,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_1,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_93,c_2])).

tff(c_230,plain,(
    ! [D_161,C_162] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_161,C_162)),D_161)
      | ~ m1_subset_1(D_161,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_162,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_161,C_162) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_161,C_162)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_100,c_225])).

tff(c_234,plain,(
    ! [D_161,C_162] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_161,C_162)),D_161)
      | ~ m1_subset_1(D_161,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_162,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_161,C_162) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_161,C_162)),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_230])).

tff(c_235,plain,(
    ! [D_161,C_162] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_161,C_162)),D_161)
      | ~ m1_subset_1(D_161,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_162,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_161,C_162) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_161,C_162)),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_234])).

tff(c_240,plain,(
    ! [C_167] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_167)),'#skF_5')
      | ~ m1_subset_1(C_167,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_167) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_237,c_235])).

tff(c_256,plain,(
    ! [C_167] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_167)),'#skF_5')
      | ~ m1_subset_1(C_167,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_167) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_93,c_240])).

tff(c_273,plain,(
    ! [C_172] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_172)),'#skF_5')
      | ~ m1_subset_1(C_172,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_172) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_256])).

tff(c_28,plain,(
    ! [A_46,D_74,B_62,E_76] :
      ( r3_orders_2(A_46,k1_funct_1(D_74,u1_struct_0(A_46)),B_62)
      | ~ r2_hidden(B_62,E_76)
      | ~ m2_orders_2(E_76,A_46,D_74)
      | ~ m1_orders_1(D_74,k1_orders_1(u1_struct_0(A_46)))
      | ~ m1_subset_1(k1_funct_1(D_74,u1_struct_0(A_46)),u1_struct_0(A_46))
      | ~ m1_subset_1(B_62,u1_struct_0(A_46))
      | ~ l1_orders_2(A_46)
      | ~ v5_orders_2(A_46)
      | ~ v4_orders_2(A_46)
      | ~ v3_orders_2(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_921,plain,(
    ! [A_328,D_329,C_330] :
      ( r3_orders_2(A_328,k1_funct_1(D_329,u1_struct_0(A_328)),'#skF_1'(k3_orders_2('#skF_2','#skF_5',C_330)))
      | ~ m2_orders_2('#skF_5',A_328,D_329)
      | ~ m1_orders_1(D_329,k1_orders_1(u1_struct_0(A_328)))
      | ~ m1_subset_1(k1_funct_1(D_329,u1_struct_0(A_328)),u1_struct_0(A_328))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_330)),u1_struct_0(A_328))
      | ~ l1_orders_2(A_328)
      | ~ v5_orders_2(A_328)
      | ~ v4_orders_2(A_328)
      | ~ v3_orders_2(A_328)
      | v2_struct_0(A_328)
      | ~ m1_subset_1(C_330,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_330) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_273,c_28])).

tff(c_926,plain,(
    ! [C_330] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_330)))
      | ~ m2_orders_2('#skF_5','#skF_2','#skF_4')
      | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k1_funct_1('#skF_4',u1_struct_0('#skF_2')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_330)),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_330,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_330) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_921])).

tff(c_929,plain,(
    ! [C_330] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_330)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_330)),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_330,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_330) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_32,c_36,c_34,c_926])).

tff(c_931,plain,(
    ! [C_331] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_331)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_331)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_331,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_331) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_929])).

tff(c_935,plain,(
    ! [C_131] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_131)))
      | ~ m1_subset_1(C_131,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_131) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_144,c_931])).

tff(c_941,plain,(
    ! [C_131] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_131)))
      | ~ m1_subset_1(C_131,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_131) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_93,c_935])).

tff(c_944,plain,(
    ! [C_332] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_332)))
      | ~ m1_subset_1(C_332,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_332) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_941])).

tff(c_18,plain,(
    ! [A_21,B_22,C_23] :
      ( r1_orders_2(A_21,B_22,C_23)
      | ~ r3_orders_2(A_21,B_22,C_23)
      | ~ m1_subset_1(C_23,u1_struct_0(A_21))
      | ~ m1_subset_1(B_22,u1_struct_0(A_21))
      | ~ l1_orders_2(A_21)
      | ~ v3_orders_2(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_946,plain,(
    ! [C_332] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_332)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_332)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_332,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_332) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_944,c_18])).

tff(c_949,plain,(
    ! [C_332] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_332)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_332)),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_332,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_332) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_38,c_946])).

tff(c_951,plain,(
    ! [C_333] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_333)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_333)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_333,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_333) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_949])).

tff(c_955,plain,(
    ! [C_131] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_131)))
      | ~ m1_subset_1(C_131,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_131) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_144,c_951])).

tff(c_961,plain,(
    ! [C_131] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_131)))
      | ~ m1_subset_1(C_131,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_131) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_93,c_955])).

tff(c_964,plain,(
    ! [C_334] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_334)))
      | ~ m1_subset_1(C_334,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_334) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_961])).

tff(c_169,plain,(
    ! [A_139,B_140,C_141,D_142] :
      ( r2_orders_2(A_139,B_140,C_141)
      | ~ r2_hidden(B_140,k3_orders_2(A_139,D_142,C_141))
      | ~ m1_subset_1(D_142,k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ m1_subset_1(C_141,u1_struct_0(A_139))
      | ~ m1_subset_1(B_140,u1_struct_0(A_139))
      | ~ l1_orders_2(A_139)
      | ~ v5_orders_2(A_139)
      | ~ v4_orders_2(A_139)
      | ~ v3_orders_2(A_139)
      | v2_struct_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_695,plain,(
    ! [A_283,D_284,C_285] :
      ( r2_orders_2(A_283,'#skF_1'(k3_orders_2(A_283,D_284,C_285)),C_285)
      | ~ m1_subset_1(D_284,k1_zfmisc_1(u1_struct_0(A_283)))
      | ~ m1_subset_1(C_285,u1_struct_0(A_283))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_283,D_284,C_285)),u1_struct_0(A_283))
      | ~ l1_orders_2(A_283)
      | ~ v5_orders_2(A_283)
      | ~ v4_orders_2(A_283)
      | ~ v3_orders_2(A_283)
      | v2_struct_0(A_283)
      | k3_orders_2(A_283,D_284,C_285) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_169])).

tff(c_712,plain,(
    ! [A_288,B_289,C_290] :
      ( r2_orders_2(A_288,'#skF_1'(k3_orders_2(A_288,B_289,C_290)),C_290)
      | ~ m1_subset_1(C_290,u1_struct_0(A_288))
      | ~ m1_subset_1(B_289,k1_zfmisc_1(u1_struct_0(A_288)))
      | ~ l1_orders_2(A_288)
      | ~ v5_orders_2(A_288)
      | ~ v4_orders_2(A_288)
      | ~ v3_orders_2(A_288)
      | v2_struct_0(A_288)
      | k3_orders_2(A_288,B_289,C_290) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_144,c_695])).

tff(c_20,plain,(
    ! [A_24,C_30,B_28] :
      ( ~ r2_orders_2(A_24,C_30,B_28)
      | ~ r1_orders_2(A_24,B_28,C_30)
      | ~ m1_subset_1(C_30,u1_struct_0(A_24))
      | ~ m1_subset_1(B_28,u1_struct_0(A_24))
      | ~ l1_orders_2(A_24)
      | ~ v5_orders_2(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_715,plain,(
    ! [A_288,C_290,B_289] :
      ( ~ r1_orders_2(A_288,C_290,'#skF_1'(k3_orders_2(A_288,B_289,C_290)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_288,B_289,C_290)),u1_struct_0(A_288))
      | ~ m1_subset_1(C_290,u1_struct_0(A_288))
      | ~ m1_subset_1(B_289,k1_zfmisc_1(u1_struct_0(A_288)))
      | ~ l1_orders_2(A_288)
      | ~ v5_orders_2(A_288)
      | ~ v4_orders_2(A_288)
      | ~ v3_orders_2(A_288)
      | v2_struct_0(A_288)
      | k3_orders_2(A_288,B_289,C_290) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_712,c_20])).

tff(c_967,plain,
    ( ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_964,c_715])).

tff(c_973,plain,
    ( ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_46,c_44,c_42,c_40,c_93,c_967])).

tff(c_974,plain,(
    ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_48,c_973])).

tff(c_981,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_144,c_974])).

tff(c_987,plain,
    ( v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_93,c_38,c_981])).

tff(c_989,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_48,c_987])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:38:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.74/1.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.99/1.69  
% 3.99/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.99/1.69  %$ r3_orders_2 > r2_orders_2 > r1_orders_2 > m2_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k4_tarski > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.99/1.69  
% 3.99/1.69  %Foreground sorts:
% 3.99/1.69  
% 3.99/1.69  
% 3.99/1.69  %Background operators:
% 3.99/1.69  
% 3.99/1.69  
% 3.99/1.69  %Foreground operators:
% 3.99/1.69  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.99/1.69  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 3.99/1.69  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.99/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.99/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.99/1.69  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.99/1.69  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.99/1.69  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.99/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.99/1.69  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 3.99/1.69  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 3.99/1.69  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 3.99/1.69  tff('#skF_5', type, '#skF_5': $i).
% 3.99/1.69  tff('#skF_2', type, '#skF_2': $i).
% 3.99/1.69  tff('#skF_3', type, '#skF_3': $i).
% 3.99/1.69  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.99/1.69  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.99/1.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.99/1.69  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.99/1.69  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.99/1.69  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 3.99/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.99/1.69  tff('#skF_4', type, '#skF_4': $i).
% 3.99/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.99/1.69  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 3.99/1.69  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 3.99/1.69  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.99/1.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.99/1.69  
% 3.99/1.71  tff(f_194, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_orders_1(C, k1_orders_1(u1_struct_0(A))) => (![D]: (m2_orders_2(D, A, C) => ((B = k1_funct_1(C, u1_struct_0(A))) => (k3_orders_2(A, D, B) = k1_xboole_0)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_orders_2)).
% 3.99/1.71  tff(f_84, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 3.99/1.71  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 3.99/1.71  tff(f_64, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 3.99/1.71  tff(f_31, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.99/1.71  tff(f_140, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_orders_2)).
% 3.99/1.71  tff(f_169, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_orders_1(D, k1_orders_1(u1_struct_0(A))) => (![E]: (m2_orders_2(E, A, D) => ((r2_hidden(B, E) & (C = k1_funct_1(D, u1_struct_0(A)))) => r3_orders_2(A, C, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_orders_2)).
% 3.99/1.71  tff(f_99, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 3.99/1.71  tff(f_114, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r1_orders_2(A, B, C) & r2_orders_2(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_orders_2)).
% 3.99/1.71  tff(c_30, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.99/1.71  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.99/1.71  tff(c_46, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.99/1.71  tff(c_44, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.99/1.71  tff(c_42, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.99/1.71  tff(c_40, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.99/1.71  tff(c_36, plain, (m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.99/1.71  tff(c_34, plain, (m2_orders_2('#skF_5', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.99/1.71  tff(c_87, plain, (![C_115, A_116, B_117]: (m1_subset_1(C_115, k1_zfmisc_1(u1_struct_0(A_116))) | ~m2_orders_2(C_115, A_116, B_117) | ~m1_orders_1(B_117, k1_orders_1(u1_struct_0(A_116))) | ~l1_orders_2(A_116) | ~v5_orders_2(A_116) | ~v4_orders_2(A_116) | ~v3_orders_2(A_116) | v2_struct_0(A_116))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.99/1.71  tff(c_89, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_87])).
% 3.99/1.71  tff(c_92, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_36, c_89])).
% 3.99/1.71  tff(c_93, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_48, c_92])).
% 3.99/1.71  tff(c_38, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.99/1.71  tff(c_4, plain, (![A_4]: (r2_hidden('#skF_1'(A_4), A_4) | k1_xboole_0=A_4)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.99/1.71  tff(c_94, plain, (![A_118, B_119, C_120]: (m1_subset_1(k3_orders_2(A_118, B_119, C_120), k1_zfmisc_1(u1_struct_0(A_118))) | ~m1_subset_1(C_120, u1_struct_0(A_118)) | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_orders_2(A_118) | ~v5_orders_2(A_118) | ~v4_orders_2(A_118) | ~v3_orders_2(A_118) | v2_struct_0(A_118))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.99/1.71  tff(c_2, plain, (![A_1, C_3, B_2]: (m1_subset_1(A_1, C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.99/1.71  tff(c_140, plain, (![A_128, A_129, B_130, C_131]: (m1_subset_1(A_128, u1_struct_0(A_129)) | ~r2_hidden(A_128, k3_orders_2(A_129, B_130, C_131)) | ~m1_subset_1(C_131, u1_struct_0(A_129)) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_orders_2(A_129) | ~v5_orders_2(A_129) | ~v4_orders_2(A_129) | ~v3_orders_2(A_129) | v2_struct_0(A_129))), inference(resolution, [status(thm)], [c_94, c_2])).
% 3.99/1.71  tff(c_144, plain, (![A_129, B_130, C_131]: (m1_subset_1('#skF_1'(k3_orders_2(A_129, B_130, C_131)), u1_struct_0(A_129)) | ~m1_subset_1(C_131, u1_struct_0(A_129)) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_orders_2(A_129) | ~v5_orders_2(A_129) | ~v4_orders_2(A_129) | ~v3_orders_2(A_129) | v2_struct_0(A_129) | k3_orders_2(A_129, B_130, C_131)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_140])).
% 3.99/1.71  tff(c_32, plain, (k1_funct_1('#skF_4', u1_struct_0('#skF_2'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.99/1.71  tff(c_145, plain, (![B_132, D_133, A_134, C_135]: (r2_hidden(B_132, D_133) | ~r2_hidden(B_132, k3_orders_2(A_134, D_133, C_135)) | ~m1_subset_1(D_133, k1_zfmisc_1(u1_struct_0(A_134))) | ~m1_subset_1(C_135, u1_struct_0(A_134)) | ~m1_subset_1(B_132, u1_struct_0(A_134)) | ~l1_orders_2(A_134) | ~v5_orders_2(A_134) | ~v4_orders_2(A_134) | ~v3_orders_2(A_134) | v2_struct_0(A_134))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.99/1.71  tff(c_225, plain, (![A_160, D_161, C_162]: (r2_hidden('#skF_1'(k3_orders_2(A_160, D_161, C_162)), D_161) | ~m1_subset_1(D_161, k1_zfmisc_1(u1_struct_0(A_160))) | ~m1_subset_1(C_162, u1_struct_0(A_160)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_160, D_161, C_162)), u1_struct_0(A_160)) | ~l1_orders_2(A_160) | ~v5_orders_2(A_160) | ~v4_orders_2(A_160) | ~v3_orders_2(A_160) | v2_struct_0(A_160) | k3_orders_2(A_160, D_161, C_162)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_145])).
% 3.99/1.71  tff(c_237, plain, (![A_165, B_166, C_167]: (r2_hidden('#skF_1'(k3_orders_2(A_165, B_166, C_167)), B_166) | ~m1_subset_1(C_167, u1_struct_0(A_165)) | ~m1_subset_1(B_166, k1_zfmisc_1(u1_struct_0(A_165))) | ~l1_orders_2(A_165) | ~v5_orders_2(A_165) | ~v4_orders_2(A_165) | ~v3_orders_2(A_165) | v2_struct_0(A_165) | k3_orders_2(A_165, B_166, C_167)=k1_xboole_0)), inference(resolution, [status(thm)], [c_144, c_225])).
% 3.99/1.71  tff(c_100, plain, (![A_1]: (m1_subset_1(A_1, u1_struct_0('#skF_2')) | ~r2_hidden(A_1, '#skF_5'))), inference(resolution, [status(thm)], [c_93, c_2])).
% 3.99/1.71  tff(c_230, plain, (![D_161, C_162]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_161, C_162)), D_161) | ~m1_subset_1(D_161, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_162, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_161, C_162)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_161, C_162)), '#skF_5'))), inference(resolution, [status(thm)], [c_100, c_225])).
% 3.99/1.71  tff(c_234, plain, (![D_161, C_162]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_161, C_162)), D_161) | ~m1_subset_1(D_161, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_162, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_161, C_162)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_161, C_162)), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_230])).
% 3.99/1.71  tff(c_235, plain, (![D_161, C_162]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_161, C_162)), D_161) | ~m1_subset_1(D_161, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_162, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_161, C_162)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_161, C_162)), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_48, c_234])).
% 3.99/1.71  tff(c_240, plain, (![C_167]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_167)), '#skF_5') | ~m1_subset_1(C_167, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_167)=k1_xboole_0)), inference(resolution, [status(thm)], [c_237, c_235])).
% 3.99/1.71  tff(c_256, plain, (![C_167]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_167)), '#skF_5') | ~m1_subset_1(C_167, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_167)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_93, c_240])).
% 3.99/1.71  tff(c_273, plain, (![C_172]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_172)), '#skF_5') | ~m1_subset_1(C_172, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_172)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_48, c_256])).
% 3.99/1.71  tff(c_28, plain, (![A_46, D_74, B_62, E_76]: (r3_orders_2(A_46, k1_funct_1(D_74, u1_struct_0(A_46)), B_62) | ~r2_hidden(B_62, E_76) | ~m2_orders_2(E_76, A_46, D_74) | ~m1_orders_1(D_74, k1_orders_1(u1_struct_0(A_46))) | ~m1_subset_1(k1_funct_1(D_74, u1_struct_0(A_46)), u1_struct_0(A_46)) | ~m1_subset_1(B_62, u1_struct_0(A_46)) | ~l1_orders_2(A_46) | ~v5_orders_2(A_46) | ~v4_orders_2(A_46) | ~v3_orders_2(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.99/1.71  tff(c_921, plain, (![A_328, D_329, C_330]: (r3_orders_2(A_328, k1_funct_1(D_329, u1_struct_0(A_328)), '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_330))) | ~m2_orders_2('#skF_5', A_328, D_329) | ~m1_orders_1(D_329, k1_orders_1(u1_struct_0(A_328))) | ~m1_subset_1(k1_funct_1(D_329, u1_struct_0(A_328)), u1_struct_0(A_328)) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_330)), u1_struct_0(A_328)) | ~l1_orders_2(A_328) | ~v5_orders_2(A_328) | ~v4_orders_2(A_328) | ~v3_orders_2(A_328) | v2_struct_0(A_328) | ~m1_subset_1(C_330, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_330)=k1_xboole_0)), inference(resolution, [status(thm)], [c_273, c_28])).
% 3.99/1.71  tff(c_926, plain, (![C_330]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_330))) | ~m2_orders_2('#skF_5', '#skF_2', '#skF_4') | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_funct_1('#skF_4', u1_struct_0('#skF_2')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_330)), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(C_330, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_330)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_921])).
% 3.99/1.71  tff(c_929, plain, (![C_330]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_330))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_330)), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_330, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_330)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_32, c_36, c_34, c_926])).
% 3.99/1.71  tff(c_931, plain, (![C_331]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_331))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_331)), u1_struct_0('#skF_2')) | ~m1_subset_1(C_331, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_331)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_48, c_929])).
% 3.99/1.71  tff(c_935, plain, (![C_131]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_131))) | ~m1_subset_1(C_131, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_131)=k1_xboole_0)), inference(resolution, [status(thm)], [c_144, c_931])).
% 3.99/1.71  tff(c_941, plain, (![C_131]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_131))) | ~m1_subset_1(C_131, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_131)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_93, c_935])).
% 3.99/1.71  tff(c_944, plain, (![C_332]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_332))) | ~m1_subset_1(C_332, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_332)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_48, c_941])).
% 3.99/1.71  tff(c_18, plain, (![A_21, B_22, C_23]: (r1_orders_2(A_21, B_22, C_23) | ~r3_orders_2(A_21, B_22, C_23) | ~m1_subset_1(C_23, u1_struct_0(A_21)) | ~m1_subset_1(B_22, u1_struct_0(A_21)) | ~l1_orders_2(A_21) | ~v3_orders_2(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.99/1.71  tff(c_946, plain, (![C_332]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_332))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_332)), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(C_332, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_332)=k1_xboole_0)), inference(resolution, [status(thm)], [c_944, c_18])).
% 3.99/1.71  tff(c_949, plain, (![C_332]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_332))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_332)), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_332, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_332)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_38, c_946])).
% 3.99/1.71  tff(c_951, plain, (![C_333]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_333))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_333)), u1_struct_0('#skF_2')) | ~m1_subset_1(C_333, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_333)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_48, c_949])).
% 3.99/1.71  tff(c_955, plain, (![C_131]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_131))) | ~m1_subset_1(C_131, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_131)=k1_xboole_0)), inference(resolution, [status(thm)], [c_144, c_951])).
% 3.99/1.71  tff(c_961, plain, (![C_131]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_131))) | ~m1_subset_1(C_131, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_131)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_93, c_955])).
% 3.99/1.71  tff(c_964, plain, (![C_334]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_334))) | ~m1_subset_1(C_334, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_334)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_48, c_961])).
% 3.99/1.71  tff(c_169, plain, (![A_139, B_140, C_141, D_142]: (r2_orders_2(A_139, B_140, C_141) | ~r2_hidden(B_140, k3_orders_2(A_139, D_142, C_141)) | ~m1_subset_1(D_142, k1_zfmisc_1(u1_struct_0(A_139))) | ~m1_subset_1(C_141, u1_struct_0(A_139)) | ~m1_subset_1(B_140, u1_struct_0(A_139)) | ~l1_orders_2(A_139) | ~v5_orders_2(A_139) | ~v4_orders_2(A_139) | ~v3_orders_2(A_139) | v2_struct_0(A_139))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.99/1.71  tff(c_695, plain, (![A_283, D_284, C_285]: (r2_orders_2(A_283, '#skF_1'(k3_orders_2(A_283, D_284, C_285)), C_285) | ~m1_subset_1(D_284, k1_zfmisc_1(u1_struct_0(A_283))) | ~m1_subset_1(C_285, u1_struct_0(A_283)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_283, D_284, C_285)), u1_struct_0(A_283)) | ~l1_orders_2(A_283) | ~v5_orders_2(A_283) | ~v4_orders_2(A_283) | ~v3_orders_2(A_283) | v2_struct_0(A_283) | k3_orders_2(A_283, D_284, C_285)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_169])).
% 3.99/1.71  tff(c_712, plain, (![A_288, B_289, C_290]: (r2_orders_2(A_288, '#skF_1'(k3_orders_2(A_288, B_289, C_290)), C_290) | ~m1_subset_1(C_290, u1_struct_0(A_288)) | ~m1_subset_1(B_289, k1_zfmisc_1(u1_struct_0(A_288))) | ~l1_orders_2(A_288) | ~v5_orders_2(A_288) | ~v4_orders_2(A_288) | ~v3_orders_2(A_288) | v2_struct_0(A_288) | k3_orders_2(A_288, B_289, C_290)=k1_xboole_0)), inference(resolution, [status(thm)], [c_144, c_695])).
% 3.99/1.71  tff(c_20, plain, (![A_24, C_30, B_28]: (~r2_orders_2(A_24, C_30, B_28) | ~r1_orders_2(A_24, B_28, C_30) | ~m1_subset_1(C_30, u1_struct_0(A_24)) | ~m1_subset_1(B_28, u1_struct_0(A_24)) | ~l1_orders_2(A_24) | ~v5_orders_2(A_24))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.99/1.71  tff(c_715, plain, (![A_288, C_290, B_289]: (~r1_orders_2(A_288, C_290, '#skF_1'(k3_orders_2(A_288, B_289, C_290))) | ~m1_subset_1('#skF_1'(k3_orders_2(A_288, B_289, C_290)), u1_struct_0(A_288)) | ~m1_subset_1(C_290, u1_struct_0(A_288)) | ~m1_subset_1(B_289, k1_zfmisc_1(u1_struct_0(A_288))) | ~l1_orders_2(A_288) | ~v5_orders_2(A_288) | ~v4_orders_2(A_288) | ~v3_orders_2(A_288) | v2_struct_0(A_288) | k3_orders_2(A_288, B_289, C_290)=k1_xboole_0)), inference(resolution, [status(thm)], [c_712, c_20])).
% 3.99/1.71  tff(c_967, plain, (~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_964, c_715])).
% 3.99/1.71  tff(c_973, plain, (~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_46, c_44, c_42, c_40, c_93, c_967])).
% 3.99/1.71  tff(c_974, plain, (~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_30, c_48, c_973])).
% 3.99/1.71  tff(c_981, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_144, c_974])).
% 3.99/1.71  tff(c_987, plain, (v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_93, c_38, c_981])).
% 3.99/1.71  tff(c_989, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_48, c_987])).
% 3.99/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.99/1.71  
% 3.99/1.71  Inference rules
% 3.99/1.71  ----------------------
% 3.99/1.71  #Ref     : 0
% 3.99/1.71  #Sup     : 165
% 3.99/1.71  #Fact    : 0
% 3.99/1.71  #Define  : 0
% 3.99/1.71  #Split   : 2
% 3.99/1.71  #Chain   : 0
% 3.99/1.71  #Close   : 0
% 3.99/1.71  
% 3.99/1.71  Ordering : KBO
% 3.99/1.71  
% 3.99/1.71  Simplification rules
% 3.99/1.71  ----------------------
% 3.99/1.71  #Subsume      : 53
% 3.99/1.71  #Demod        : 318
% 3.99/1.71  #Tautology    : 22
% 3.99/1.71  #SimpNegUnit  : 69
% 3.99/1.71  #BackRed      : 14
% 3.99/1.71  
% 3.99/1.71  #Partial instantiations: 0
% 3.99/1.71  #Strategies tried      : 1
% 3.99/1.71  
% 3.99/1.71  Timing (in seconds)
% 3.99/1.71  ----------------------
% 3.99/1.71  Preprocessing        : 0.35
% 3.99/1.71  Parsing              : 0.20
% 3.99/1.71  CNF conversion       : 0.03
% 3.99/1.71  Main loop            : 0.54
% 3.99/1.71  Inferencing          : 0.22
% 3.99/1.71  Reduction            : 0.15
% 3.99/1.71  Demodulation         : 0.10
% 3.99/1.71  BG Simplification    : 0.03
% 3.99/1.71  Subsumption          : 0.11
% 3.99/1.71  Abstraction          : 0.02
% 3.99/1.71  MUC search           : 0.00
% 3.99/1.71  Cooper               : 0.00
% 3.99/1.71  Total                : 0.93
% 3.99/1.72  Index Insertion      : 0.00
% 3.99/1.72  Index Deletion       : 0.00
% 3.99/1.72  Index Matching       : 0.00
% 3.99/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
