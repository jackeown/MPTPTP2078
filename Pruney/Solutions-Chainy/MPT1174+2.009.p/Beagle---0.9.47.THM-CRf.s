%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:53 EST 2020

% Result     : Theorem 3.92s
% Output     : CNFRefutation 3.92s
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
%$ r3_orders_2 > r2_orders_2 > r1_orders_2 > m2_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k3_mcart_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_orders_2)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_orders_2)).

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
    ! [C_123,A_124,B_125] :
      ( m1_subset_1(C_123,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ m2_orders_2(C_123,A_124,B_125)
      | ~ m1_orders_1(B_125,k1_orders_1(u1_struct_0(A_124)))
      | ~ l1_orders_2(A_124)
      | ~ v5_orders_2(A_124)
      | ~ v4_orders_2(A_124)
      | ~ v3_orders_2(A_124)
      | v2_struct_0(A_124) ) ),
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
    ! [A_126,B_127,C_128] :
      ( m1_subset_1(k3_orders_2(A_126,B_127,C_128),k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ m1_subset_1(C_128,u1_struct_0(A_126))
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_orders_2(A_126)
      | ~ v5_orders_2(A_126)
      | ~ v4_orders_2(A_126)
      | ~ v3_orders_2(A_126)
      | v2_struct_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( m1_subset_1(A_1,C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_140,plain,(
    ! [A_136,A_137,B_138,C_139] :
      ( m1_subset_1(A_136,u1_struct_0(A_137))
      | ~ r2_hidden(A_136,k3_orders_2(A_137,B_138,C_139))
      | ~ m1_subset_1(C_139,u1_struct_0(A_137))
      | ~ m1_subset_1(B_138,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ l1_orders_2(A_137)
      | ~ v5_orders_2(A_137)
      | ~ v4_orders_2(A_137)
      | ~ v3_orders_2(A_137)
      | v2_struct_0(A_137) ) ),
    inference(resolution,[status(thm)],[c_94,c_2])).

tff(c_144,plain,(
    ! [A_137,B_138,C_139] :
      ( m1_subset_1('#skF_1'(k3_orders_2(A_137,B_138,C_139)),u1_struct_0(A_137))
      | ~ m1_subset_1(C_139,u1_struct_0(A_137))
      | ~ m1_subset_1(B_138,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ l1_orders_2(A_137)
      | ~ v5_orders_2(A_137)
      | ~ v4_orders_2(A_137)
      | ~ v3_orders_2(A_137)
      | v2_struct_0(A_137)
      | k3_orders_2(A_137,B_138,C_139) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_140])).

tff(c_32,plain,(
    k1_funct_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_145,plain,(
    ! [B_140,D_141,A_142,C_143] :
      ( r2_hidden(B_140,D_141)
      | ~ r2_hidden(B_140,k3_orders_2(A_142,D_141,C_143))
      | ~ m1_subset_1(D_141,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ m1_subset_1(C_143,u1_struct_0(A_142))
      | ~ m1_subset_1(B_140,u1_struct_0(A_142))
      | ~ l1_orders_2(A_142)
      | ~ v5_orders_2(A_142)
      | ~ v4_orders_2(A_142)
      | ~ v3_orders_2(A_142)
      | v2_struct_0(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_225,plain,(
    ! [A_170,D_171,C_172] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_170,D_171,C_172)),D_171)
      | ~ m1_subset_1(D_171,k1_zfmisc_1(u1_struct_0(A_170)))
      | ~ m1_subset_1(C_172,u1_struct_0(A_170))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_170,D_171,C_172)),u1_struct_0(A_170))
      | ~ l1_orders_2(A_170)
      | ~ v5_orders_2(A_170)
      | ~ v4_orders_2(A_170)
      | ~ v3_orders_2(A_170)
      | v2_struct_0(A_170)
      | k3_orders_2(A_170,D_171,C_172) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_145])).

tff(c_237,plain,(
    ! [A_175,B_176,C_177] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_175,B_176,C_177)),B_176)
      | ~ m1_subset_1(C_177,u1_struct_0(A_175))
      | ~ m1_subset_1(B_176,k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ l1_orders_2(A_175)
      | ~ v5_orders_2(A_175)
      | ~ v4_orders_2(A_175)
      | ~ v3_orders_2(A_175)
      | v2_struct_0(A_175)
      | k3_orders_2(A_175,B_176,C_177) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_144,c_225])).

tff(c_100,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_1,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_93,c_2])).

tff(c_230,plain,(
    ! [D_171,C_172] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_171,C_172)),D_171)
      | ~ m1_subset_1(D_171,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_172,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_171,C_172) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_171,C_172)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_100,c_225])).

tff(c_234,plain,(
    ! [D_171,C_172] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_171,C_172)),D_171)
      | ~ m1_subset_1(D_171,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_172,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_171,C_172) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_171,C_172)),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_230])).

tff(c_235,plain,(
    ! [D_171,C_172] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_171,C_172)),D_171)
      | ~ m1_subset_1(D_171,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_172,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_171,C_172) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_171,C_172)),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_234])).

tff(c_240,plain,(
    ! [C_177] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_177)),'#skF_5')
      | ~ m1_subset_1(C_177,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_177) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_237,c_235])).

tff(c_256,plain,(
    ! [C_177] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_177)),'#skF_5')
      | ~ m1_subset_1(C_177,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_177) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_93,c_240])).

tff(c_273,plain,(
    ! [C_182] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_182)),'#skF_5')
      | ~ m1_subset_1(C_182,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_182) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_256])).

tff(c_28,plain,(
    ! [A_50,D_78,B_66,E_80] :
      ( r3_orders_2(A_50,k1_funct_1(D_78,u1_struct_0(A_50)),B_66)
      | ~ r2_hidden(B_66,E_80)
      | ~ m2_orders_2(E_80,A_50,D_78)
      | ~ m1_orders_1(D_78,k1_orders_1(u1_struct_0(A_50)))
      | ~ m1_subset_1(k1_funct_1(D_78,u1_struct_0(A_50)),u1_struct_0(A_50))
      | ~ m1_subset_1(B_66,u1_struct_0(A_50))
      | ~ l1_orders_2(A_50)
      | ~ v5_orders_2(A_50)
      | ~ v4_orders_2(A_50)
      | ~ v3_orders_2(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_921,plain,(
    ! [A_350,D_351,C_352] :
      ( r3_orders_2(A_350,k1_funct_1(D_351,u1_struct_0(A_350)),'#skF_1'(k3_orders_2('#skF_2','#skF_5',C_352)))
      | ~ m2_orders_2('#skF_5',A_350,D_351)
      | ~ m1_orders_1(D_351,k1_orders_1(u1_struct_0(A_350)))
      | ~ m1_subset_1(k1_funct_1(D_351,u1_struct_0(A_350)),u1_struct_0(A_350))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_352)),u1_struct_0(A_350))
      | ~ l1_orders_2(A_350)
      | ~ v5_orders_2(A_350)
      | ~ v4_orders_2(A_350)
      | ~ v3_orders_2(A_350)
      | v2_struct_0(A_350)
      | ~ m1_subset_1(C_352,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_352) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_273,c_28])).

tff(c_926,plain,(
    ! [C_352] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_352)))
      | ~ m2_orders_2('#skF_5','#skF_2','#skF_4')
      | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k1_funct_1('#skF_4',u1_struct_0('#skF_2')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_352)),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_352,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_352) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_921])).

tff(c_929,plain,(
    ! [C_352] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_352)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_352)),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_352,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_352) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_32,c_36,c_34,c_926])).

tff(c_931,plain,(
    ! [C_353] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_353)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_353)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_353,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_353) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_929])).

tff(c_935,plain,(
    ! [C_139] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_139)))
      | ~ m1_subset_1(C_139,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_139) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_144,c_931])).

tff(c_941,plain,(
    ! [C_139] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_139)))
      | ~ m1_subset_1(C_139,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_139) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_93,c_935])).

tff(c_944,plain,(
    ! [C_354] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_354)))
      | ~ m1_subset_1(C_354,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_354) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_941])).

tff(c_18,plain,(
    ! [A_25,B_26,C_27] :
      ( r1_orders_2(A_25,B_26,C_27)
      | ~ r3_orders_2(A_25,B_26,C_27)
      | ~ m1_subset_1(C_27,u1_struct_0(A_25))
      | ~ m1_subset_1(B_26,u1_struct_0(A_25))
      | ~ l1_orders_2(A_25)
      | ~ v3_orders_2(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_946,plain,(
    ! [C_354] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_354)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_354)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_354,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_354) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_944,c_18])).

tff(c_949,plain,(
    ! [C_354] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_354)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_354)),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_354,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_354) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_38,c_946])).

tff(c_951,plain,(
    ! [C_355] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_355)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_355)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_355,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_355) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_949])).

tff(c_955,plain,(
    ! [C_139] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_139)))
      | ~ m1_subset_1(C_139,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_139) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_144,c_951])).

tff(c_961,plain,(
    ! [C_139] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_139)))
      | ~ m1_subset_1(C_139,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_139) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_93,c_955])).

tff(c_964,plain,(
    ! [C_356] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_356)))
      | ~ m1_subset_1(C_356,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_356) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_961])).

tff(c_169,plain,(
    ! [A_147,B_148,C_149,D_150] :
      ( r2_orders_2(A_147,B_148,C_149)
      | ~ r2_hidden(B_148,k3_orders_2(A_147,D_150,C_149))
      | ~ m1_subset_1(D_150,k1_zfmisc_1(u1_struct_0(A_147)))
      | ~ m1_subset_1(C_149,u1_struct_0(A_147))
      | ~ m1_subset_1(B_148,u1_struct_0(A_147))
      | ~ l1_orders_2(A_147)
      | ~ v5_orders_2(A_147)
      | ~ v4_orders_2(A_147)
      | ~ v3_orders_2(A_147)
      | v2_struct_0(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_695,plain,(
    ! [A_305,D_306,C_307] :
      ( r2_orders_2(A_305,'#skF_1'(k3_orders_2(A_305,D_306,C_307)),C_307)
      | ~ m1_subset_1(D_306,k1_zfmisc_1(u1_struct_0(A_305)))
      | ~ m1_subset_1(C_307,u1_struct_0(A_305))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_305,D_306,C_307)),u1_struct_0(A_305))
      | ~ l1_orders_2(A_305)
      | ~ v5_orders_2(A_305)
      | ~ v4_orders_2(A_305)
      | ~ v3_orders_2(A_305)
      | v2_struct_0(A_305)
      | k3_orders_2(A_305,D_306,C_307) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_169])).

tff(c_712,plain,(
    ! [A_310,B_311,C_312] :
      ( r2_orders_2(A_310,'#skF_1'(k3_orders_2(A_310,B_311,C_312)),C_312)
      | ~ m1_subset_1(C_312,u1_struct_0(A_310))
      | ~ m1_subset_1(B_311,k1_zfmisc_1(u1_struct_0(A_310)))
      | ~ l1_orders_2(A_310)
      | ~ v5_orders_2(A_310)
      | ~ v4_orders_2(A_310)
      | ~ v3_orders_2(A_310)
      | v2_struct_0(A_310)
      | k3_orders_2(A_310,B_311,C_312) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_144,c_695])).

tff(c_20,plain,(
    ! [A_28,C_34,B_32] :
      ( ~ r2_orders_2(A_28,C_34,B_32)
      | ~ r1_orders_2(A_28,B_32,C_34)
      | ~ m1_subset_1(C_34,u1_struct_0(A_28))
      | ~ m1_subset_1(B_32,u1_struct_0(A_28))
      | ~ l1_orders_2(A_28)
      | ~ v5_orders_2(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_715,plain,(
    ! [A_310,C_312,B_311] :
      ( ~ r1_orders_2(A_310,C_312,'#skF_1'(k3_orders_2(A_310,B_311,C_312)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_310,B_311,C_312)),u1_struct_0(A_310))
      | ~ m1_subset_1(C_312,u1_struct_0(A_310))
      | ~ m1_subset_1(B_311,k1_zfmisc_1(u1_struct_0(A_310)))
      | ~ l1_orders_2(A_310)
      | ~ v5_orders_2(A_310)
      | ~ v4_orders_2(A_310)
      | ~ v3_orders_2(A_310)
      | v2_struct_0(A_310)
      | k3_orders_2(A_310,B_311,C_312) = k1_xboole_0 ) ),
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
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:48:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.92/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/1.72  
% 3.92/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/1.72  %$ r3_orders_2 > r2_orders_2 > r1_orders_2 > m2_orders_2 > v6_orders_2 > r2_hidden > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k3_mcart_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.92/1.72  
% 3.92/1.72  %Foreground sorts:
% 3.92/1.72  
% 3.92/1.72  
% 3.92/1.72  %Background operators:
% 3.92/1.72  
% 3.92/1.72  
% 3.92/1.72  %Foreground operators:
% 3.92/1.72  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.92/1.72  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 3.92/1.72  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.92/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.92/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.92/1.72  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.92/1.72  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.92/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.92/1.72  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 3.92/1.72  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.92/1.72  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 3.92/1.72  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 3.92/1.72  tff('#skF_5', type, '#skF_5': $i).
% 3.92/1.72  tff('#skF_2', type, '#skF_2': $i).
% 3.92/1.72  tff('#skF_3', type, '#skF_3': $i).
% 3.92/1.72  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.92/1.72  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.92/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.92/1.72  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.92/1.72  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.92/1.72  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 3.92/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.92/1.72  tff('#skF_4', type, '#skF_4': $i).
% 3.92/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.92/1.72  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 3.92/1.72  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 3.92/1.72  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.92/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.92/1.72  
% 3.92/1.74  tff(f_194, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_orders_1(C, k1_orders_1(u1_struct_0(A))) => (![D]: (m2_orders_2(D, A, C) => ((B = k1_funct_1(C, u1_struct_0(A))) => (k3_orders_2(A, D, B) = k1_xboole_0)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_orders_2)).
% 3.92/1.74  tff(f_84, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 3.92/1.74  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 3.92/1.74  tff(f_64, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 3.92/1.74  tff(f_31, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.92/1.74  tff(f_140, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 3.92/1.74  tff(f_169, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_orders_1(D, k1_orders_1(u1_struct_0(A))) => (![E]: (m2_orders_2(E, A, D) => ((r2_hidden(B, E) & (C = k1_funct_1(D, u1_struct_0(A)))) => r3_orders_2(A, C, B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_orders_2)).
% 3.92/1.74  tff(f_99, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 3.92/1.74  tff(f_114, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r1_orders_2(A, B, C) & r2_orders_2(A, C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_orders_2)).
% 3.92/1.74  tff(c_30, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.92/1.74  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.92/1.74  tff(c_46, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.92/1.74  tff(c_44, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.92/1.74  tff(c_42, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.92/1.74  tff(c_40, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.92/1.74  tff(c_36, plain, (m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.92/1.74  tff(c_34, plain, (m2_orders_2('#skF_5', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.92/1.74  tff(c_87, plain, (![C_123, A_124, B_125]: (m1_subset_1(C_123, k1_zfmisc_1(u1_struct_0(A_124))) | ~m2_orders_2(C_123, A_124, B_125) | ~m1_orders_1(B_125, k1_orders_1(u1_struct_0(A_124))) | ~l1_orders_2(A_124) | ~v5_orders_2(A_124) | ~v4_orders_2(A_124) | ~v3_orders_2(A_124) | v2_struct_0(A_124))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.92/1.74  tff(c_89, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_87])).
% 3.92/1.74  tff(c_92, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_36, c_89])).
% 3.92/1.74  tff(c_93, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_48, c_92])).
% 3.92/1.74  tff(c_38, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.92/1.74  tff(c_4, plain, (![A_4]: (r2_hidden('#skF_1'(A_4), A_4) | k1_xboole_0=A_4)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.92/1.74  tff(c_94, plain, (![A_126, B_127, C_128]: (m1_subset_1(k3_orders_2(A_126, B_127, C_128), k1_zfmisc_1(u1_struct_0(A_126))) | ~m1_subset_1(C_128, u1_struct_0(A_126)) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_orders_2(A_126) | ~v5_orders_2(A_126) | ~v4_orders_2(A_126) | ~v3_orders_2(A_126) | v2_struct_0(A_126))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.92/1.74  tff(c_2, plain, (![A_1, C_3, B_2]: (m1_subset_1(A_1, C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.92/1.74  tff(c_140, plain, (![A_136, A_137, B_138, C_139]: (m1_subset_1(A_136, u1_struct_0(A_137)) | ~r2_hidden(A_136, k3_orders_2(A_137, B_138, C_139)) | ~m1_subset_1(C_139, u1_struct_0(A_137)) | ~m1_subset_1(B_138, k1_zfmisc_1(u1_struct_0(A_137))) | ~l1_orders_2(A_137) | ~v5_orders_2(A_137) | ~v4_orders_2(A_137) | ~v3_orders_2(A_137) | v2_struct_0(A_137))), inference(resolution, [status(thm)], [c_94, c_2])).
% 3.92/1.74  tff(c_144, plain, (![A_137, B_138, C_139]: (m1_subset_1('#skF_1'(k3_orders_2(A_137, B_138, C_139)), u1_struct_0(A_137)) | ~m1_subset_1(C_139, u1_struct_0(A_137)) | ~m1_subset_1(B_138, k1_zfmisc_1(u1_struct_0(A_137))) | ~l1_orders_2(A_137) | ~v5_orders_2(A_137) | ~v4_orders_2(A_137) | ~v3_orders_2(A_137) | v2_struct_0(A_137) | k3_orders_2(A_137, B_138, C_139)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_140])).
% 3.92/1.74  tff(c_32, plain, (k1_funct_1('#skF_4', u1_struct_0('#skF_2'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_194])).
% 3.92/1.74  tff(c_145, plain, (![B_140, D_141, A_142, C_143]: (r2_hidden(B_140, D_141) | ~r2_hidden(B_140, k3_orders_2(A_142, D_141, C_143)) | ~m1_subset_1(D_141, k1_zfmisc_1(u1_struct_0(A_142))) | ~m1_subset_1(C_143, u1_struct_0(A_142)) | ~m1_subset_1(B_140, u1_struct_0(A_142)) | ~l1_orders_2(A_142) | ~v5_orders_2(A_142) | ~v4_orders_2(A_142) | ~v3_orders_2(A_142) | v2_struct_0(A_142))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.92/1.74  tff(c_225, plain, (![A_170, D_171, C_172]: (r2_hidden('#skF_1'(k3_orders_2(A_170, D_171, C_172)), D_171) | ~m1_subset_1(D_171, k1_zfmisc_1(u1_struct_0(A_170))) | ~m1_subset_1(C_172, u1_struct_0(A_170)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_170, D_171, C_172)), u1_struct_0(A_170)) | ~l1_orders_2(A_170) | ~v5_orders_2(A_170) | ~v4_orders_2(A_170) | ~v3_orders_2(A_170) | v2_struct_0(A_170) | k3_orders_2(A_170, D_171, C_172)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_145])).
% 3.92/1.74  tff(c_237, plain, (![A_175, B_176, C_177]: (r2_hidden('#skF_1'(k3_orders_2(A_175, B_176, C_177)), B_176) | ~m1_subset_1(C_177, u1_struct_0(A_175)) | ~m1_subset_1(B_176, k1_zfmisc_1(u1_struct_0(A_175))) | ~l1_orders_2(A_175) | ~v5_orders_2(A_175) | ~v4_orders_2(A_175) | ~v3_orders_2(A_175) | v2_struct_0(A_175) | k3_orders_2(A_175, B_176, C_177)=k1_xboole_0)), inference(resolution, [status(thm)], [c_144, c_225])).
% 3.92/1.74  tff(c_100, plain, (![A_1]: (m1_subset_1(A_1, u1_struct_0('#skF_2')) | ~r2_hidden(A_1, '#skF_5'))), inference(resolution, [status(thm)], [c_93, c_2])).
% 3.92/1.74  tff(c_230, plain, (![D_171, C_172]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_171, C_172)), D_171) | ~m1_subset_1(D_171, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_172, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_171, C_172)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_171, C_172)), '#skF_5'))), inference(resolution, [status(thm)], [c_100, c_225])).
% 3.92/1.74  tff(c_234, plain, (![D_171, C_172]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_171, C_172)), D_171) | ~m1_subset_1(D_171, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_172, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_171, C_172)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_171, C_172)), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_230])).
% 3.92/1.74  tff(c_235, plain, (![D_171, C_172]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_171, C_172)), D_171) | ~m1_subset_1(D_171, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_172, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_171, C_172)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_171, C_172)), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_48, c_234])).
% 3.92/1.74  tff(c_240, plain, (![C_177]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_177)), '#skF_5') | ~m1_subset_1(C_177, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_177)=k1_xboole_0)), inference(resolution, [status(thm)], [c_237, c_235])).
% 3.92/1.74  tff(c_256, plain, (![C_177]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_177)), '#skF_5') | ~m1_subset_1(C_177, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_177)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_93, c_240])).
% 3.92/1.74  tff(c_273, plain, (![C_182]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_182)), '#skF_5') | ~m1_subset_1(C_182, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_182)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_48, c_256])).
% 3.92/1.74  tff(c_28, plain, (![A_50, D_78, B_66, E_80]: (r3_orders_2(A_50, k1_funct_1(D_78, u1_struct_0(A_50)), B_66) | ~r2_hidden(B_66, E_80) | ~m2_orders_2(E_80, A_50, D_78) | ~m1_orders_1(D_78, k1_orders_1(u1_struct_0(A_50))) | ~m1_subset_1(k1_funct_1(D_78, u1_struct_0(A_50)), u1_struct_0(A_50)) | ~m1_subset_1(B_66, u1_struct_0(A_50)) | ~l1_orders_2(A_50) | ~v5_orders_2(A_50) | ~v4_orders_2(A_50) | ~v3_orders_2(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.92/1.74  tff(c_921, plain, (![A_350, D_351, C_352]: (r3_orders_2(A_350, k1_funct_1(D_351, u1_struct_0(A_350)), '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_352))) | ~m2_orders_2('#skF_5', A_350, D_351) | ~m1_orders_1(D_351, k1_orders_1(u1_struct_0(A_350))) | ~m1_subset_1(k1_funct_1(D_351, u1_struct_0(A_350)), u1_struct_0(A_350)) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_352)), u1_struct_0(A_350)) | ~l1_orders_2(A_350) | ~v5_orders_2(A_350) | ~v4_orders_2(A_350) | ~v3_orders_2(A_350) | v2_struct_0(A_350) | ~m1_subset_1(C_352, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_352)=k1_xboole_0)), inference(resolution, [status(thm)], [c_273, c_28])).
% 3.92/1.74  tff(c_926, plain, (![C_352]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_352))) | ~m2_orders_2('#skF_5', '#skF_2', '#skF_4') | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_funct_1('#skF_4', u1_struct_0('#skF_2')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_352)), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(C_352, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_352)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_921])).
% 3.92/1.74  tff(c_929, plain, (![C_352]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_352))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_352)), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_352, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_352)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_32, c_36, c_34, c_926])).
% 3.92/1.74  tff(c_931, plain, (![C_353]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_353))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_353)), u1_struct_0('#skF_2')) | ~m1_subset_1(C_353, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_353)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_48, c_929])).
% 3.92/1.74  tff(c_935, plain, (![C_139]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_139))) | ~m1_subset_1(C_139, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_139)=k1_xboole_0)), inference(resolution, [status(thm)], [c_144, c_931])).
% 3.92/1.74  tff(c_941, plain, (![C_139]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_139))) | ~m1_subset_1(C_139, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_139)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_93, c_935])).
% 3.92/1.74  tff(c_944, plain, (![C_354]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_354))) | ~m1_subset_1(C_354, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_354)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_48, c_941])).
% 3.92/1.74  tff(c_18, plain, (![A_25, B_26, C_27]: (r1_orders_2(A_25, B_26, C_27) | ~r3_orders_2(A_25, B_26, C_27) | ~m1_subset_1(C_27, u1_struct_0(A_25)) | ~m1_subset_1(B_26, u1_struct_0(A_25)) | ~l1_orders_2(A_25) | ~v3_orders_2(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.92/1.74  tff(c_946, plain, (![C_354]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_354))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_354)), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(C_354, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_354)=k1_xboole_0)), inference(resolution, [status(thm)], [c_944, c_18])).
% 3.92/1.74  tff(c_949, plain, (![C_354]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_354))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_354)), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_354, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_354)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_38, c_946])).
% 3.92/1.74  tff(c_951, plain, (![C_355]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_355))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_355)), u1_struct_0('#skF_2')) | ~m1_subset_1(C_355, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_355)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_48, c_949])).
% 3.92/1.74  tff(c_955, plain, (![C_139]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_139))) | ~m1_subset_1(C_139, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_139)=k1_xboole_0)), inference(resolution, [status(thm)], [c_144, c_951])).
% 3.92/1.74  tff(c_961, plain, (![C_139]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_139))) | ~m1_subset_1(C_139, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_139)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_93, c_955])).
% 3.92/1.74  tff(c_964, plain, (![C_356]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_356))) | ~m1_subset_1(C_356, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_356)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_48, c_961])).
% 3.92/1.74  tff(c_169, plain, (![A_147, B_148, C_149, D_150]: (r2_orders_2(A_147, B_148, C_149) | ~r2_hidden(B_148, k3_orders_2(A_147, D_150, C_149)) | ~m1_subset_1(D_150, k1_zfmisc_1(u1_struct_0(A_147))) | ~m1_subset_1(C_149, u1_struct_0(A_147)) | ~m1_subset_1(B_148, u1_struct_0(A_147)) | ~l1_orders_2(A_147) | ~v5_orders_2(A_147) | ~v4_orders_2(A_147) | ~v3_orders_2(A_147) | v2_struct_0(A_147))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.92/1.74  tff(c_695, plain, (![A_305, D_306, C_307]: (r2_orders_2(A_305, '#skF_1'(k3_orders_2(A_305, D_306, C_307)), C_307) | ~m1_subset_1(D_306, k1_zfmisc_1(u1_struct_0(A_305))) | ~m1_subset_1(C_307, u1_struct_0(A_305)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_305, D_306, C_307)), u1_struct_0(A_305)) | ~l1_orders_2(A_305) | ~v5_orders_2(A_305) | ~v4_orders_2(A_305) | ~v3_orders_2(A_305) | v2_struct_0(A_305) | k3_orders_2(A_305, D_306, C_307)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_169])).
% 3.92/1.74  tff(c_712, plain, (![A_310, B_311, C_312]: (r2_orders_2(A_310, '#skF_1'(k3_orders_2(A_310, B_311, C_312)), C_312) | ~m1_subset_1(C_312, u1_struct_0(A_310)) | ~m1_subset_1(B_311, k1_zfmisc_1(u1_struct_0(A_310))) | ~l1_orders_2(A_310) | ~v5_orders_2(A_310) | ~v4_orders_2(A_310) | ~v3_orders_2(A_310) | v2_struct_0(A_310) | k3_orders_2(A_310, B_311, C_312)=k1_xboole_0)), inference(resolution, [status(thm)], [c_144, c_695])).
% 3.92/1.74  tff(c_20, plain, (![A_28, C_34, B_32]: (~r2_orders_2(A_28, C_34, B_32) | ~r1_orders_2(A_28, B_32, C_34) | ~m1_subset_1(C_34, u1_struct_0(A_28)) | ~m1_subset_1(B_32, u1_struct_0(A_28)) | ~l1_orders_2(A_28) | ~v5_orders_2(A_28))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.92/1.74  tff(c_715, plain, (![A_310, C_312, B_311]: (~r1_orders_2(A_310, C_312, '#skF_1'(k3_orders_2(A_310, B_311, C_312))) | ~m1_subset_1('#skF_1'(k3_orders_2(A_310, B_311, C_312)), u1_struct_0(A_310)) | ~m1_subset_1(C_312, u1_struct_0(A_310)) | ~m1_subset_1(B_311, k1_zfmisc_1(u1_struct_0(A_310))) | ~l1_orders_2(A_310) | ~v5_orders_2(A_310) | ~v4_orders_2(A_310) | ~v3_orders_2(A_310) | v2_struct_0(A_310) | k3_orders_2(A_310, B_311, C_312)=k1_xboole_0)), inference(resolution, [status(thm)], [c_712, c_20])).
% 3.92/1.74  tff(c_967, plain, (~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_964, c_715])).
% 3.92/1.74  tff(c_973, plain, (~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_46, c_44, c_42, c_40, c_93, c_967])).
% 3.92/1.74  tff(c_974, plain, (~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_30, c_48, c_973])).
% 3.92/1.74  tff(c_981, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_144, c_974])).
% 3.92/1.74  tff(c_987, plain, (v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_93, c_38, c_981])).
% 3.92/1.74  tff(c_989, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_48, c_987])).
% 3.92/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/1.74  
% 3.92/1.74  Inference rules
% 3.92/1.74  ----------------------
% 3.92/1.74  #Ref     : 0
% 3.92/1.74  #Sup     : 165
% 3.92/1.74  #Fact    : 0
% 3.92/1.74  #Define  : 0
% 3.92/1.74  #Split   : 2
% 3.92/1.74  #Chain   : 0
% 3.92/1.74  #Close   : 0
% 3.92/1.74  
% 3.92/1.74  Ordering : KBO
% 3.92/1.74  
% 3.92/1.74  Simplification rules
% 3.92/1.74  ----------------------
% 3.92/1.74  #Subsume      : 53
% 3.92/1.74  #Demod        : 318
% 3.92/1.74  #Tautology    : 22
% 3.92/1.74  #SimpNegUnit  : 69
% 3.92/1.74  #BackRed      : 14
% 3.92/1.74  
% 3.92/1.74  #Partial instantiations: 0
% 3.92/1.74  #Strategies tried      : 1
% 3.92/1.74  
% 3.92/1.74  Timing (in seconds)
% 3.92/1.74  ----------------------
% 3.92/1.75  Preprocessing        : 0.35
% 3.92/1.75  Parsing              : 0.20
% 3.92/1.75  CNF conversion       : 0.03
% 3.92/1.75  Main loop            : 0.55
% 3.92/1.75  Inferencing          : 0.22
% 3.92/1.75  Reduction            : 0.16
% 3.92/1.75  Demodulation         : 0.11
% 3.92/1.75  BG Simplification    : 0.03
% 3.92/1.75  Subsumption          : 0.11
% 3.92/1.75  Abstraction          : 0.03
% 3.92/1.75  MUC search           : 0.00
% 3.92/1.75  Cooper               : 0.00
% 3.92/1.75  Total                : 0.95
% 3.92/1.75  Index Insertion      : 0.00
% 3.92/1.75  Index Deletion       : 0.00
% 3.92/1.75  Index Matching       : 0.00
% 3.92/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
